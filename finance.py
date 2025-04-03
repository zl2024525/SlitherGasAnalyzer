import requests
import pandas as pd
import matplotlib.pyplot as plt
import streamlit as st

# CoinGecko API endpoint
COINGECKO_API_URL = "https://api.coingecko.com/api/v3/simple/price"

# Configure matplotlib to support English
plt.rcParams['font.sans-serif'] = ['Arial']
plt.rcParams['axes.unicode_minus'] = False


def get_eth_price():
    """
    Get the real-time Ethereum price
    """
    try:
        response = requests.get('https://api.coingecko.com/api/v3/simple/price?ids=ethereum&vs_currencies=usd')
        data = response.json()
        return data['ethereum']['usd']
    except Exception as e:
        print(f"Failed to get Ethereum price: {e}")
        return None


def calculate_gas_cost(gas_used, gas_price):
    """
    Calculate the Gas cost (in ETH)
    """
    return (gas_price * gas_used) / 1e9


def convert_to_usd(eth_cost, eth_price):
    """
    Convert the ETH cost to US dollars
    """
    if eth_price is not None:
        return eth_cost * eth_price
    return None


def visualize_cost(total_gas, eth_cost, usd_cost):
    """
    Visualize the cost information
    """
    fig, ax = plt.subplots(figsize=(8, 4))
    ax.barh(["Gas Consumption", "ETH Cost", "USD Cost"],
            [total_gas, eth_cost, usd_cost],
            color=['#4CAF50', '#2196F3', '#FF5722'])
    return fig


def main():
    st.title("Smart Contract Gas Cost and Financial Value Analysis")

    # Get the ETH price
    eth_price = get_eth_price()
    if eth_price is None:
        return

    # Assume the Gas usage and Gas price obtained from the detection tool (need to integrate with the detection tool here)
    gas_used = 100000  # Example value, need to obtain from the detection tool
    gas_price_gwei = 50  # Example value, need to obtain from the Ethereum node

    # Calculate the Gas cost
    gas_cost_eth = calculate_gas_cost(gas_used, gas_price_gwei)
    gas_cost_usd = convert_to_usd(gas_cost_eth, eth_price)

    # Display the results
    st.write(f"Gas Usage: {gas_used}")
    st.write(f"Gas Price (Gwei): {gas_price_gwei}")
    st.write(f"Gas Cost (ETH): {gas_cost_eth}")
    st.write(f"Gas Cost (USD): {gas_cost_usd}")

    # Visualize
    fig = visualize_cost(gas_used, gas_cost_eth, gas_cost_usd)
    st.pyplot(fig)


if __name__ == "__main__":
    main()
