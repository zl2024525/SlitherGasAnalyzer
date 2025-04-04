# SlitherGasAnalyzer: Smart Contract Gas Waste Detection Tool
SlitherGasAnalyzer is a specialized tool designed to detect Gas-wasting patterns in smart contracts. Leveraging the power of Slither for AST (Abstract Syntax Tree) analysis, it offers in-depth insights into areas of Gas inefficiency within Solidity smart contracts. This tool is not only a user-friendly solution for optimizing contract costs but also a valuable asset for financial institutions and audit agencies.

## Key Features
* **Advanced Gas-Waste Detection:** Utilizes Slither's AST analysis to identify 8 core Gas-wasting patterns, such as accessing storage variables inside loops, loops without unchecked blocks, and redundant conditional checks.
* **Real-Time Financial Calculations:** The finance.py module enables real-time conversion of Gas consumption to USD costs. It fetches the latest ETH price and calculates Gas costs in both ETH and USD, providing a clear financial perspective on Gas waste.
* **Multi-File Processing:** Supports batch upload of smart contract files. The tool automatically adapts to different Solidity compiler versions using solc-select integration, ensuring seamless analysis across a wide range of projects.
* **Interactive Visual Interface:** Built on Streamlit, the app.py offers an intuitive interactive interface. It generates detailed reports on Gas waste analysis, including visualizations of issue statistics and provides actionable optimization suggestions.
* **Data Persistence:** The AnalysisDB class in app.py enables the storage and retrieval of historical analysis results.










