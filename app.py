import streamlit as st
import pandas as pd
import matplotlib.pyplot as plt
import sqlite3
import json
from datetime import datetime
from detectors import analyze_contract
import io
import shutil
from zipfile import ZipFile
import os
import re
import traceback
from pathlib import Path
from semantic_version import Version, Spec
from crytic_compile import CryticCompile
import subprocess
import asyncio
from finance import get_eth_price, calculate_gas_cost, convert_to_usd

# Initialize the global Web3 instance
WEB3_INSTANCE = None


# ---------- Initialization functions ---------- #
def initialize_web3():
    """Synchronously initialize the Web3 connection"""
    global WEB3_INSTANCE
    try:
        # Create an event loop for the current thread
        try:
            loop = asyncio.get_running_loop()
        except RuntimeError:
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)

        from web3 import Web3

        infura_id = os.getenv("INFURA_PROJECT_ID")
        if not infura_id:
            raise ValueError("INFURA_PROJECT_ID environment variable not detected")

        provider_url = f"https://mainnet.infura.io/v3/{infura_id}"
        WEB3_INSTANCE = Web3(Web3.HTTPProvider(provider_url))

        if not WEB3_INSTANCE.is_connected():
            raise ConnectionError("Unable to connect to the Ethereum network")

        print("✔️ Web3 connection successful")
        return True
    except Exception as e:
        st.error(f"Web3 initialization failed: {str(e)}")
        st.stop()


# ---------- Core analysis functions ---------- #
class ContractAnalyzer:
    def __init__(self):
        self.optimization_tips = {
            "Accessing storage variables inside loops": "🔄 It is recommended to cache storage variables into memory variables to reduce SLOAD/SSTORE operations",
            "Loops without unchecked": "⚡ Use an unchecked block to wrap loops that are guaranteed not to overflow",
            "Repeated state variable reads": "📦 Cache repeatedly read variables into local variables",
            "High Gas mathematical operations": "🔄 Use bitwise shifts or lookup tables for mathematical operations",
            "Redundant conditional checks": "🧾 Combine repeated require checks",
            "Not using storage pointers": "🔗 For cases where different members of the same index of the same storage array are accessed consecutively, use storage pointers for optimization",
            "Large memory array parameters": "💡 Consider changing large memory array parameters to calldata to save Gas",
            "Analysis error": "❌ Please check if the contract syntax is correct"
        }

        self.installed_versions = self._get_installed_solc_versions()

    def _get_installed_solc_versions(self):
        """Get the installed solc versions"""
        try:
            result = subprocess.run(
                ['solc-select', 'versions'],
                capture_output=True,
                text=True
            )
            return re.findall(r'(\d+\.\d+\.\d+)', result.stdout)
        except Exception as e:
            st.error(f"Failed to get compiler versions: {str(e)}")
            return []

    def _get_compatible_version(self, version_spec):
        """Get the compatible compiler version"""
        try:
            if version_spec.startswith('='):
                version_spec = version_spec[1:].strip()
            spec = Spec(version_spec)
            for ver in self.installed_versions:
                if Version(ver) in spec:
                    return ver
            return None
        except ValueError:
            return None

    def analyze_single_file(self, file_path):
        """Analyze a single contract file"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()

            # Extract the version specification
            version_specs = re.findall(
                r'pragma\s+solidity\s+([^;]+);',
                content
            )

            if not version_specs:
                raise ValueError("No valid solidity version declaration found")

            # Select the latest version declaration
            latest_version = self._find_latest_version(version_specs)
            compatible_version = self._get_compatible_version(latest_version)

            if not compatible_version:
                raise ValueError(f"No compatible compiler version found: {latest_version}")

            # Set the compiler version
            os.environ['SOLC_VERSION'] = compatible_version
            print(f"Using compiler version: {compatible_version}")

            # Directly call the detectors module for analysis
            # Note: Here, the single file path is wrapped in a list and passed to the analyze_contract function
            issues = analyze_contract([file_path])
            return issues

        except Exception as e:
            traceback.print_exc()
            raise RuntimeError(f"File analysis failed: {str(e)}")

    def analyze_contract_with_version(self, file_path):
        """Analyze the contract using the specified compiler version"""
        try:
            version_specs = []
            with open(file_path, 'r', encoding='utf-8') as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith('//'):
                        continue
                    if "pragma solidity" in line:
                        if '//' in line:
                            line = line.split('//')[0].strip()
                        start_index = line.find("pragma solidity") + len("pragma solidity")
                        version_part = line[start_index:].strip()
                        if version_part.endswith(';'):
                            version_part = version_part[:-1]
                        version_specs.append(version_part)

            if not version_specs:
                raise ValueError(f"No valid pragma solidity directive found in {file_path}")

            # Select the latest version declaration
            latest_version = self._find_latest_version(version_specs)
            print(f"Extracted version range from contract file {file_path}: {latest_version}")

            compatible_version = self._get_compatible_version(latest_version)
            if compatible_version:
                version = compatible_version
                print(f"Selected compatible version number: {version}")
            else:
                raise ValueError(
                    f"No installed version compatible with {latest_version} found. Please use 'solc-select install {latest_version.lstrip('^~><= ')}' to install.")

            os.environ['SOLC_VERSION'] = version
            print(f"Set SOLC_VERSION to: {version}")

            crytic_compile = CryticCompile(file_path, solc_version=version)

            return analyze_contract([file_path])
        except Exception as e:
            if "Version" in str(e) and "not installed" in str(e):
                error_message = f"The required Solidity compiler version {version} is not installed. Please use 'solc-select install {version}' to install."
            else:
                error_message = f"File analysis failed: {str(e)}"
            print(error_message)
            return []

    def _find_latest_version(self, version_specs):
        valid_versions = []
        for spec in version_specs:
            try:
                # Try to parse the version
                if spec.startswith('='):
                    spec = spec[1:].strip()
                # Simple processing, take the first matching version
                possible_version = re.search(r'(\d+\.\d+\.\d+)', spec)
                if possible_version:
                    valid_versions.append(Version(possible_version.group(1)))
            except ValueError:
                continue
        if valid_versions:
            return str(max(valid_versions))
        else:
            raise ValueError("No valid version declaration found")


# ---------- Data persistence ---------- #
class AnalysisDB:
    def __init__(self, db_name="analysis_history.db"):
        self.conn = sqlite3.connect(db_name)
        self._init_db()

    def _init_db(self):
        """Initialize the database table structure"""
        self.conn.execute('''CREATE TABLE IF NOT EXISTS analysis_history
                           (id INTEGER PRIMARY KEY AUTOINCREMENT,
                            filenames TEXT,
                            timestamp TEXT,
                            stats TEXT,
                            issues TEXT,
                            eth_price REAL,
                            gas_price REAL,
                            total_gas INTEGER,
                            eth_cost REAL,
                            usd_cost REAL)''')
        self.conn.commit()

    def save_result(self, result):
        """Save the analysis result"""
        try:
            self.conn.execute('''INSERT INTO analysis_history 
                                (filenames, timestamp, stats, issues, eth_price, gas_price, total_gas, eth_cost, usd_cost)
                                VALUES (?,?,?,?,?,?,?,?,?)''',
                              (json.dumps(result["filenames"]),
                               result["timestamp"],
                               json.dumps(result["stats"]),
                               json.dumps(result["issues"]),
                               result["eth_price"],
                               result["gas_price"],
                               result["total_gas"],
                               result["eth_cost"],
                               result["usd_cost"]))
            self.conn.commit()
            return True
        except Exception as e:
            print(f"Database save failed: {str(e)}")
            return False

    def load_history(self):
        """Load the historical records"""
        try:
            cursor = self.conn.cursor()
            cursor.execute("SELECT * FROM analysis_history ORDER BY timestamp DESC")
            return [
                {
                    "id": row[0],
                    "filenames": json.loads(row[1]),
                    "timestamp": row[2],
                    "stats": json.loads(row[3]),
                    "issues": json.loads(row[4]),
                    "eth_price": row[5],
                    "gas_price": row[6],
                    "total_gas": row[7],
                    "eth_cost": row[8],
                    "usd_cost": row[9]
                }
                for row in cursor.fetchall()
            ]
        except Exception as e:
            print(f"Database query failed: {str(e)}")
            return []


# ---------- UI components ---------- #
class UIComponents:
    def __init__(self):
        self.db = AnalysisDB()
        self.analyzer = ContractAnalyzer()
        if 'current_result' not in st.session_state:
            st.session_state.current_result = None
        if 'selected_history' not in st.session_state:
            st.session_state.selected_history = None
        if 'prev_uploaded_files' not in st.session_state:
            st.session_state.prev_uploaded_files = None
        if 'current_page' not in st.session_state:
            st.session_state.current_page = "Contract Analysis"

    def _clean_temp_files(self):
        temp_dir = Path("uploads")
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
            print("Temporary files have been cleaned")

    def show_gas_analysis(self, result):
        st.markdown("### 📊 Gas Consumption Analysis")
        eth_price = result["eth_price"]
        gas_price = result["gas_price"]
        total_gas = result["total_gas"]
        eth_cost = result["eth_cost"]
        usd_cost = result["usd_cost"]

        st.markdown("**Total Gas Consumption**")
        st.write(f"{total_gas:,} Gas")

        st.markdown("**ETH Cost**")
        st.write(f"Ξ{eth_cost:.18f}")

        st.markdown("**USD Estimation**")
        st.write(f"${usd_cost:.18f}")

        # Display the current Gas price, real - time Ethereum dollar price, and conversion information
        st.markdown("###### Current Network Information")
        eth_per_gas = gas_price / 1e18
        st.write(f"Current 1 Gas = {gas_price} Wei")
        st.write(f"Current 1 Gas = {eth_per_gas:.18f} ETH")
        st.write(f"Current 1 ETH = ${eth_price:.5f}")

        # Cancel the visualization of the Gas consumption analysis
        return None

    def show_optimization_tips(self, issue_type):
        return self.analyzer.optimization_tips.get(
            issue_type,
            "ℹ️ Please refer to the official Solidity optimization guide"
        )

    def _calculate_stats(self, analysis_results):
        stats = {}
        for issue in analysis_results:
            issue_type = issue["type"]
            if issue_type in stats:
                stats[issue_type] += 1
            else:
                stats[issue_type] = 1
        return stats

    def main_analysis_page(self):
        st.title("🔍 Smart Contract Gas Optimization Analysis")
        uploaded_files = st.file_uploader(
            "Upload Solidity contract files",
            type=["sol"],
            accept_multiple_files=True,
            key="file_uploader"
        )
        if uploaded_files:
            if st.session_state.prev_uploaded_files != uploaded_files:
                st.session_state.current_result = None
                st.session_state.prev_uploaded_files = uploaded_files
            if st.button("Start Analysis", type="primary"):
                self._clean_temp_files()
                initialize_web3()
                try:
                    file_paths = []
                    for file in uploaded_files:
                        save_path = Path("uploads") / file.name
                        save_path.parent.mkdir(exist_ok=True)
                        with open(save_path, "wb") as f:
                            f.write(file.getbuffer())
                        file_paths.append(str(save_path))
                    analysis_results = []
                    for path in file_paths:
                        issues = self.analyzer.analyze_contract_with_version(path)
                        analysis_results.extend(issues)
                    eth_price = get_eth_price()
                    gas_price = WEB3_INSTANCE.eth.gas_price
                    if not all([eth_price, gas_price]):
                        st.warning("Unable to obtain real - time on - chain data")
                        return
                    total_gas = sum(issue.get("gas_used", 0) for issue in analysis_results)
                    gas_price_gwei = gas_price / 1e9  # Convert gas_price from Wei to Gwei
                    eth_cost = calculate_gas_cost(total_gas, gas_price_gwei)
                    usd_cost = convert_to_usd(eth_cost, eth_price)
                    final_result = {
                        "filenames": [Path(p).name for p in file_paths],
                        "timestamp": datetime.now().strftime('%Y-%m-%dT%H:%M:%S'),
                        "stats": self._calculate_stats(analysis_results),
                        "issues": analysis_results,
                        "eth_price": eth_price,
                        "gas_price": gas_price,
                        "total_gas": total_gas,
                        "eth_cost": eth_cost,
                        "usd_cost": usd_cost
                    }
                    self.db.save_result(final_result)
                    st.session_state.current_result = final_result
                    st.success("Analysis completed!")
                except Exception as e:
                    st.error(f"An error occurred during the analysis: {str(e)}")
                    st.code(traceback.format_exc())
        if st.session_state.current_result:
            self.show_analysis_result(st.session_state.current_result)
            self.add_export_buttons(st.session_state.current_result)

    def show_analysis_result(self, result):
        """Display the complete analysis result"""
        self.show_gas_analysis(result)

        # Issue statistics
        st.markdown("### 📊 Issue Statistics")
        if result["stats"]:
            non_zero_stats = {k: v for k, v in result["stats"].items() if v > 0}
            if non_zero_stats:
                df_stats = pd.DataFrame(list(non_zero_stats.items()), columns=["Issue Type", "Quantity"])
                # Set the index to start from 1
                df_stats.index = df_stats.index + 1
                # Set the figure size
                fig, ax = plt.subplots(figsize=(5, 5))
                wedges, texts, autotexts = ax.pie(df_stats["Quantity"], labels=df_stats["Issue Type"],
                                                  autopct='%1.1f%%')
                # Modify the legend position, font size, and legend title size
                legend = ax.legend(wedges, df_stats["Issue Type"], title="Issue Type", loc="upper center",
                                   bbox_to_anchor=(0.9, 1.4), prop={'size': 6}, title_fontsize=8)
                # Adjust the position of the pie chart
                ax.set_position([0.1, 0.2, 0.5, 0.5])
                st.pyplot(fig)
                # Add a table to display the issue quantity, with a smaller and centered title
                st.markdown(
                    "<h4 style='text-align: center;font-size: 16px;font-weight: bold;'>Issue Quantity Statistics Table</h4>",
                    unsafe_allow_html=True)
                st.table(df_stats)
            else:
                st.success("🎉 No optimization points detected")
        else:
            st.success("🎉 No optimization points detected")

        # Optimization suggestions summary
        st.markdown("### 📋 Optimization Suggestions Summary")
        if result["issues"]:
            df = pd.DataFrame(result["issues"])
            st.dataframe(
                df[["type", "location", "description", "gas_used"]],
                use_container_width=True,
                hide_index=True
            )
        else:
            st.success("🎉 No optimizable items detected")

        # Only return the fig when there are issue statistics
        if result["stats"] and {k: v for k, v in result["stats"].items() if v > 0}:
            return fig
        else:
            return None

    def history_page(self):
        """History page"""
        st.title("📜 Analysis History")

        history = self.db.load_history()
        if not history:
            st.info("No historical records available")
            return

        # Number of records displayed per page
        records_per_page = 5
        # Calculate the total number of pages
        total_pages = len(history) // records_per_page + (1 if len(history) % records_per_page != 0 else 0)

        # Initialize the current page number
        if 'current_page_num' not in st.session_state:
            st.session_state.current_page_num = 1
        else:
            # Check if current_page_num is a valid integer representation
            if isinstance(st.session_state.current_page_num, str) and st.session_state.current_page_num.isdigit():
                st.session_state.current_page_num = int(st.session_state.current_page_num)
            elif isinstance(st.session_state.current_page_num, int):
                pass
            else:
                st.session_state.current_page_num = 1

        # Calculate the start and end indices of the current page
        start_index = (st.session_state.current_page_num - 1) * records_per_page
        end_index = start_index + records_per_page

        # Display the current page number information
        st.markdown(f"Showing page {st.session_state.current_page_num} of {total_pages}")

        # Display the list of historical records (click to select)
        for record in history[start_index:end_index]:
            if st.button(
                    f"{', '.join(record['filenames'])} - {record['timestamp']}",
                    key=f"history_{record['id']}"
            ):
                st.session_state.selected_history = record

        # Pagination buttons
        col1, col2 = st.columns(2)

        with col1:
            if st.button("<-", disabled=st.session_state.current_page_num <= 1):
                st.session_state.current_page_num -= 1
                st.rerun()

        with col2:
            if st.button("->", disabled=st.session_state.current_page_num >= total_pages):
                st.session_state.current_page_num += 1
                st.rerun()

        # Action button area
        st.markdown("---")
        col1, col2, col3 = st.columns(3)

        with col1:
            if st.button("View Selected Record"):
                if st.session_state.selected_history:
                    st.session_state.current_result = st.session_state.selected_history
                    st.rerun()
                else:
                    st.warning("Please select a record first")

        with col2:
            if st.button("Delete Selected Record"):
                if st.session_state.selected_history:
                    try:
                        self.db.conn.execute("DELETE FROM analysis_history WHERE id =?",
                                             (st.session_state.selected_history["id"],))
                        self.db.conn.commit()
                        st.success("Record deleted successfully")
                        st.session_state.selected_history = None
                        st.session_state.current_result = None
                        st.rerun()
                    except Exception as e:
                        st.error(f"Error deleting record: {str(e)}")
                else:
                    st.warning("Please select a record first")

        with col3:
            if st.button("Export Selected Record"):
                if st.session_state.selected_history:
                    self.export_selected_record(st.session_state.selected_history)
                else:
                    st.warning("Please select a record first")

        # Display the detailed information of the selected record
        if st.session_state.current_result:
            st.subheader("Detailed Analysis Result")
            self.show_analysis_result(st.session_state.current_result)

    def add_export_buttons(self, result):
        col1, col2 = st.columns(2)
        with col1:
            if st.button("Export Diagram"):
                non_zero_stats = {k: v for k, v in result["stats"].items() if v > 0}
                if non_zero_stats:
                    df_stats = pd.DataFrame(list(non_zero_stats.items()), columns=["Issue Type", "Quantity"])
                    fig, ax = plt.subplots(figsize=(7, 5))
                    wedges, texts, autotexts = ax.pie(df_stats["Quantity"], labels=df_stats["Issue Type"],
                                                      autopct='%1.1f%%')
                    legend = ax.legend(wedges, df_stats["Issue Type"], title="Issue Type", loc="upper center",
                                       bbox_to_anchor=(0.9, 1.4), prop={'size': 6}, title_fontsize=8)
                    ax.set_position([0.2, 0.2, 0.5, 0.5])
                    img = io.BytesIO()
                    fig.savefig(img, format='png')
                    img.seek(0)
                    self.download_file(img.getvalue(), "issue_stats.png", "image/png")
                else:
                    st.warning("No issue statistics data to export")
        with col2:
            if st.button("Export Statistics Table"):
                buffer = io.StringIO()
                # Add Gas consumption analysis
                buffer.write("Gas Consumption Analysis:\n")
                gas_analysis_df = pd.DataFrame({
                    "Indicator": ["Total Gas Consumption", "ETH Cost", "USD Estimation"],
                    "Value": [f"{result['total_gas']:,} Gas", f"{result['eth_cost']:.18f}",
                              f"${result['usd_cost']:.5f}"]
                })
                gas_analysis_df.to_csv(buffer, index=False)
                buffer.write("\n\n\n\n")

                # Add current network information
                buffer.write("Current Network Information:\n")
                eth_per_gas = result["gas_price"] / 1e18
                network_info_df = pd.DataFrame({
                    "Indicator": ["Current 1 Gas (Wei)", "Current 1 Gas (ETH)", "Current 1 ETH (USD)"],
                    "Value": [result["gas_price"], f"{eth_per_gas:.18f}", f"${result['eth_price']:.5f}"]
                })
                network_info_df.to_csv(buffer, index=False)
                buffer.write("\n\n\n\n")

                # Add issue quantity statistics table
                buffer.write("Issue Quantity Statistics Table:\n")
                if result["stats"]:
                    stats_df = pd.DataFrame(list(result["stats"].items()), columns=["Issue Type", "Quantity"])
                    stats_df.to_csv(buffer, index=False)
                else:
                    buffer.write("No optimization points detected\n")
                buffer.write("\n\n\n\n")

                # Add optimization suggestions summary
                buffer.write("Optimization Suggestions Summary:\n")
                if result["issues"]:
                    issues_df = pd.DataFrame(result["issues"])
                    issues_df.to_csv(buffer, index=False)
                else:
                    buffer.write("No optimizable items detected\n")
                buffer.seek(0)
                self.download_file(buffer.getvalue().encode(), "analysis_summary.csv", "text/csv")

    def export_selected_record(self, record):
        zip_buffer = io.BytesIO()
        with ZipFile(zip_buffer, 'w') as zipf:
            # Export the issue statistics diagram
            non_zero_stats = {k: v for k, v in record["stats"].items() if v > 0}
            if non_zero_stats:
                df_stats = pd.DataFrame(list(non_zero_stats.items()), columns=["Issue Type", "Quantity"])
                fig, ax = plt.subplots(figsize=(7, 5))
                wedges, texts, autotexts = ax.pie(df_stats["Quantity"], labels=df_stats["Issue Type"],
                                                  autopct='%1.1f%%')
                legend = ax.legend(wedges, df_stats["Issue Type"], title="Issue Type", loc="upper center",
                                   bbox_to_anchor=(0.9, 1.4), prop={'size': 6}, title_fontsize=8)
                ax.set_position([0.2, 0.2, 0.5, 0.5])
                img = io.BytesIO()
                fig.savefig(img, format='png')
                img.seek(0)
                zipf.writestr("issue_stats.png", img.getvalue())

            # Export the optimization suggestions and issue statistics table
            buffer = io.StringIO()
            # Add Gas consumption analysis
            buffer.write("Gas Waste Analysis:\n")
            gas_analysis_df = pd.DataFrame({
                "Indicator": ["Total Gas Consumption", "ETH Cost", "USD Estimation"],
                "Value": [f"{record['total_gas']:,} Gas", f"{record['eth_cost']:.18f}", f"${record['usd_cost']:.5f}"]
            })
            gas_analysis_df.to_csv(buffer, index=False)
            buffer.write("\n\n\n\n")

            # Add current network information
            buffer.write("Current Network Information:\n")
            eth_per_gas = record["gas_price"] / 1e18
            network_info_df = pd.DataFrame({
                "Indicator": ["Current 1 Gas (Wei)", "Current 1 Gas (ETH)", "Current 1 ETH (USD)"],
                "Value": [record["gas_price"], f"{eth_per_gas:.18f}", f"${record['eth_price']:.5f}"]
            })
            network_info_df.to_csv(buffer, index=False)
            buffer.write("\n\n\n\n")

            # Add issue quantity statistics table
            buffer.write("Issue Quantity Statistics Table:\n")
            if record["stats"]:
                stats_df = pd.DataFrame(list(record["stats"].items()), columns=["Issue Type", "Quantity"])
                stats_df.to_csv(buffer, index=False)
            else:
                buffer.write("No optimization points detected\n")
            buffer.write("\n\n\n\n")

            # Add optimization suggestions summary
            buffer.write("Optimization Suggestions Summary:\n")
            if record["issues"]:
                issues_df = pd.DataFrame(record["issues"])
                issues_df.to_csv(buffer, index=False)
            else:
                buffer.write("No optimizable items detected\n")
            buffer.seek(0)
            zipf.writestr("analysis_summary.csv", buffer.getvalue())

        zip_buffer.seek(0)
        self.download_file(zip_buffer.getvalue(), "analysis_record.zip", "application/zip")

    def download_file(self, data, filename, mimetype):
        import base64
        b64 = base64.b64encode(data).decode()
        js = f"""
            var link = document.createElement('a');
            link.href = 'data:{mimetype};base64,{b64}';
            link.download = '{filename}';
            link.click();
        """
        st.components.v1.html(f"<script>{js}</script>", height=0)


# ---------- Application entry point ---------- #
if __name__ == "__main__":
    ui = UIComponents()

    st.sidebar.title("Navigation Menu")
    page = st.sidebar.radio("Select Page", ["Contract Analysis", "History"])

    if page != st.session_state.current_page:
        st.session_state.current_page = page
        st.session_state.current_result = None
        st.session_state.selected_history = None
        st.session_state.prev_uploaded_files = None

    if page == "Contract Analysis":
        ui.main_analysis_page()
    else:
        ui.history_page()

    st.sidebar.markdown("---")
    st.sidebar.info("""
    **User Guide**:
    1. Upload the Solidity contract files to be analyzed.
    2. View the real-time Gas waste estimation.
    3. Improve the contract according to the optimization suggestions.
    4. View past analyses in the history records.
    """)
