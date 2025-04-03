import re
import subprocess
from semantic_version import Version, Spec
from typing import List


def get_pragma_versions(file_path: str) -> List[str]:
    """
    Get all pragma solidity version declarations from the contract file.
    """
    pragma_versions = []
    try:
        with open(file_path, 'r', encoding='utf-8') as file:
            for line in file:
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
                    pragma_versions.append(version_part)
    except UnicodeDecodeError:
        print(f"Failed to read file {file_path} with utf-8 encoding. Please check the file encoding.")
    return pragma_versions


def get_compatible_version(pragma_versions: List[str], installed_versions: List[str]) -> str:
    """
    Get the compatible installed compiler version based on the pragma version declarations.
    """
    compatible_versions = []
    for version_spec in pragma_versions:
        try:
            if version_spec.startswith('='):
                version_spec = version_spec[1:].strip()
            spec = Spec(version_spec)
            for ver in installed_versions:
                if Version(ver) in spec:
                    compatible_versions.append(ver)
        except ValueError:
            continue

    if compatible_versions:
        # Sort by version number and select the largest version
        compatible_versions.sort(key=lambda v: Version(v), reverse=True)
        return compatible_versions[0]
    return ""


def get_installed_solc_versions() -> List[str]:
    """
    Get the installed solc versions.
    """
    try:
        result = subprocess.run(
            ['solc-select', 'versions'],
            capture_output=True,
            text=True
        )
        return re.findall(r'(\d+\.\d+\.\d+)', result.stdout)
    except Exception as e:
        print(f"Failed to get compiler versions: {str(e)}")
        return []


def analyze_contract(file_paths: List[str]):
    installed_versions = get_installed_solc_versions()
    for file_path in file_paths:
        pragma_versions = get_pragma_versions(file_path)
        if not pragma_versions:
            print(f"Could not determine the pragma version of {file_path}")
            continue

        compatible_version = get_compatible_version(pragma_versions, installed_versions)
        if not compatible_version:
            print(f"No installed compiler version compatible with the pragma version of {file_path} was found")
            continue

        try:
            subprocess.run(f'solc-select use {compatible_version}', shell=True, check=True)
            result = subprocess.run(f'slither {file_path}', shell=True, capture_output=True, text=True)
            # Print the standard output information of slither, including detected vulnerabilities
            if result.stdout:
                print(f"Analysis result of {file_path}:")
                print(result.stdout)
            # Print the standard error output information of slither to check for hidden errors
            if result.stderr:
                print(result.stderr)
        except subprocess.CalledProcessError as e:
            print(f"An error occurred while analyzing {file_path}: {str(e)}")


# Usage example
contract_files = ['zs7.sol']  # You can add multiple contract files, separated by commas
analyze_contract(contract_files)
