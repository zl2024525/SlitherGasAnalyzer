# SlitherGasAnalyzer: Smart Contract Gas Waste Detection Tool
SlitherGasAnalyzer is a specialized tool designed to detect Gas-wasting patterns in smart contracts. Leveraging the power of Slither for AST (Abstract Syntax Tree) analysis, it offers in-depth insights into areas of Gas inefficiency within Solidity smart contracts. This tool is not only a user-friendly solution for optimizing contract costs but also a valuable asset for financial institutions and audit agencies.

## Key Features
* **Advanced Gas-Waste Detection:** Utilizes Slither's AST analysis to identify 8 core Gas-wasting patterns, such as accessing storage variables inside loops, loops without unchecked blocks, and redundant conditional checks.
* **Real-Time Financial Calculations:** The finance.py module enables real-time conversion of Gas consumption to USD costs. It fetches the latest ETH price and calculates Gas costs in both ETH and USD, providing a clear financial perspective on Gas waste.
* **Multi-File Processing:** Supports batch upload of smart contract files. The tool automatically adapts to different Solidity compiler versions using solc-select integration, ensuring seamless analysis across a wide range of projects.
* **Interactive Visual Interface:** Built on Streamlit, the app.py offers an intuitive interactive interface. It generates detailed reports on Gas waste analysis, including visualizations of issue statistics and provides actionable optimization suggestions.
* **Data Persistence:** The AnalysisDB class in app.py enables the storage and retrieval of historical analysis results.

## Installation
### Prerequisites
* Python 3.7 or higher
* Install required Python packages:
```bash
pip install streamlit slither-io semantic-version crytic-compile requests pandas matplotlib sqlite3
```
* Install solc-select for Solidity compiler version management.

### Clone the Repository
```bash
git clone https://github.com/zl2024525/SlitherGasAnalyzer.git
cd SlitherGasAnalyzer
```

### Set up Environment Variables
* Create a .env file in the root directory of the project.
* Add your INFURA_PROJECT_ID if you plan to use the Ethereum network connection in the tool:
```bash
INFURA_PROJECT_ID = your-infura-project-id
```

## Usage
### Running the Application
* Start the Streamlit application:
```bash
streamlit run app.py
```
* A browser window will open, presenting the SlitherGasAnalyzer interface.

### Contract Analysis
* On the "Contract Analysis" page, upload one or more Solidity contract files(*.sol).
* Click the "Start Analysis" button. The tool will analyze the contracts, detect Gas-wasting patterns, calculate Gas costs, and display the results.
* The results include Gas consumption analysis, issue statistics (presented as a pie chart and a table), and optimization suggestions.

### Analysis History
* Navigate to the "History" page in the sidebar. Here, you can view a list of past analysis results.
* Click on a specific record to view its detailed analysis. You can also delete or export selected records.

## Note
About VersusOriginalSlither.py: This file can be used to compare the results of SlitherGasAnalyzer with the original Slither tool. It analyzes smart contracts using the original Slither and shows that SlitherGasAnalyzer is more focused on Gas-waste detection, while the original Slither is mainly for security vulnerability analysis.
