from slither import Slither
from pathlib import Path
from slither.core.variables.state_variable import StateVariable
from slither.core.cfg.node import NodeType
import traceback
from slither.core.solidity_types.array_type import ArrayType
import re

print("All NodeType attributes:")
for attr in dir(NodeType):
    if not attr.startswith('__'):
        print(attr)


def is_in_unchecked_block(node):
    """Check if the node is inside an unchecked block"""
    current_node = node
    while current_node:
        if current_node.expression and str(current_node.expression).startswith("unchecked"):
            return True
        current_node = getattr(current_node, 'parent', None)
        if current_node is None:
            break
    return False


def _get_location(node, file_path):
    """Uniformly handle location information extraction"""
    try:
        lines = node.source_mapping.lines
        if isinstance(lines, list):
            line_no = lines[0]
        else:
            line_no = lines
        return f"{Path(file_path).name}:{line_no}"
    except Exception:
        return f"{Path(file_path).name}:unknown"


def detect_unchecked_loops(function, file_path):
    """Detect loops without using unchecked"""
    issues = []
    loop_types = [NodeType.STARTLOOP]
    for node in function.nodes:
        if node.type in loop_types:
            if not is_in_unchecked_block(node):
                location = _get_location(node, file_path)
                # More reasonably estimate the Gas usage, assuming 1000 Gas is wasted per loop, and here assume 10 loops
                gas_used = 1000 * 10
                issues.append({
                    "type": "Loops without unchecked",
                    "description": f"An optimizable loop structure was found in function {function.name}",
                    "location": location,
                    "gas_used": gas_used  # Add the gas_used field
                })
    return issues


def detect_loop_storage_variable_access(function, file_path):
    """Detect access to storage variables inside loops (enhanced version)"""
    issues = []
    loop_types = [NodeType.IFLOOP, NodeType.STARTLOOP]

    for node in function.nodes:
        if node.type in loop_types:
            storage_ops = []
            for ir in node.irs:
                if hasattr(ir, 'read') and hasattr(ir, 'written'):
                    storage_ops.extend([v for v in ir.read + ir.written if isinstance(v, StateVariable)])
            storage_ops.extend(
                [v for v in node.state_variables_read + node.state_variables_written if isinstance(v, StateVariable)])

            for var in set(storage_ops):
                # Assume 500 Gas is wasted each time a storage variable is accessed, and here assume 5 accesses
                gas_used = 500 * 5
                issues.append({
                    "type": "Accessing storage variables inside loops",
                    "description": f"Frequent access to storage variable {var.name} in the loop",
                    "location": _get_location(node, file_path),
                    "gas_used": gas_used  # Add the gas_used field
                })
    return issues


def detect_duplicate_state_variable_read(function, file_path):
    """Detect duplicate state variable reads"""
    issues = []
    var_read_count = {}
    for node in function.nodes:
        for var in node.state_variables_read:
            if isinstance(var, StateVariable):
                var_read_count[var] = var_read_count.get(var, 0) + 1
                if var_read_count[var] > 1:
                    location = _get_location(node, file_path)
                    # Assume 300 Gas is wasted each time a duplicate read occurs, and here assume 3 duplicate reads
                    gas_used = 300 * 3
                    issues.append({
                        "type": "Repeated state variable reads",
                        "description": f"Variable {var.name} is read multiple times within the function",
                        "location": location,
                        "gas_used": gas_used  # Add the gas_used field
                    })
    return issues


def detect_high_gas_math_operations(function, file_path):
    """Detect high Gas mathematical operations"""
    issues = []
    for node in function.nodes:
        expression = str(node.expression)
        if '**' in expression:
            location = _get_location(node, file_path)
            # Assume 2000 Gas is wasted each time a high Gas mathematical operation occurs, and here assume 2 such operations
            gas_used = 2000 * 2
            issues.append({
                "type": "High Gas mathematical operations",
                "description": f"Used the high Gas ** operator. It is recommended to use bitwise shifts or lookup tables instead.",
                "location": location,
                "gas_used": gas_used  # Add the gas_used field
            })
    return issues


def detect_redundant_condition_checks(function, file_path):
    """Detect redundant conditional checks"""
    issues = []
    require_conditions = []
    for node in function.nodes:
        expression = str(node.expression)
        if expression.startswith("require"):
            # Extract the condition part of the require statement
            start_index = expression.find('(') + 1
            end_index = expression.rfind(')')
            condition = expression[start_index:end_index]
            if condition in require_conditions:
                location = _get_location(node, file_path)
                # Assume 800 Gas is wasted each time a redundant conditional check occurs, and here assume 2 redundancies
                gas_used = 800 * 2
                issues.append({
                    "type": "Redundant conditional checks",
                    "description": f"Duplicate require checks. It is recommended to merge the conditions.",
                    "location": location,
                    "gas_used": gas_used  # Add the gas_used field
                })
            else:
                require_conditions.append(condition)
    return issues


def detect_unused_storage_pointer(function, file_path):
    """Detect consecutive storage accesses without using storage pointers (enhanced version)"""
    issues = []
    access_records = {}

    for node in function.nodes:
        if node.expression and isinstance(node.expression, tuple):
            expr_str = str(node.expression[-1])  # Get the actual expression
        else:
            expr_str = str(node.expression)

        # Match any indexed access to a storage array
        pattern = re.compile(r'(storage\w+)\s*\[\s*\d+\s*\]')
        matches = pattern.findall(expr_str)

        for array_name in matches:
            key = f"{array_name}_access"
            if key in access_records:
                prev_node = access_records[key]
                if abs(node.source_mapping.lines[0] - prev_node.source_mapping.lines[0]) < 3:
                    # Assume 1500 Gas is wasted each time a storage pointer is not used, and here assume 2 such cases
                    gas_used = 1500 * 2
                    issues.append({
                        "type": "Not using storage pointers",
                        "description": f"Consecutive accesses to the same index position of {array_name} were detected.",
                        "location": _get_location(node, file_path),
                        "gas_used": gas_used  # Add the gas_used field
                    })
            access_records[key] = node
    return issues


def detect_large_memory_array(function, file_path):
    """Detect large memory array parameters (enhanced version)"""
    issues = []

    for param in function.parameters:
        # Check if it is a memory array
        if param.location == "memory" and isinstance(param.type, ArrayType):
            # Dynamic array detection
            if param.type.is_dynamic:
                # Assume 3000 Gas is wasted for a dynamic memory array
                gas_used = 3000
                issues.append({
                    "type": "Large memory array parameters",
                    "description": f"Parameter {param.name} is a dynamic memory array. It is recommended to use calldata instead.",
                    "location": _get_location(function, file_path),
                    "gas_used": gas_used  # Add the gas_used field
                })
            # Fixed-length array detection
            elif param.type.length > 32:
                # Assume 4000 Gas is wasted for a large memory fixed-length array
                gas_used = 4000
                issues.append({
                    "type": "Large memory array parameters",
                    "description": f"Parameter {param.name} uses a large memory array (size: {param.type.length})",
                    "location": _get_location(function, file_path),
                    "gas_used": gas_used  # Add the gas_used field
                })
    return issues


def analyze_contract(file_paths):
    """Analyze multiple contract files"""
    issues = []

    for file_path in file_paths:
        try:
            slither = Slither(file_path)

            for contract in slither.contracts:
                for function in contract.functions:
                    # Detect loops without using unchecked
                    issues.extend(detect_unchecked_loops(function, file_path))

                    # Detect access to storage variables inside loops
                    issues.extend(detect_loop_storage_variable_access(function, file_path))

                    # Detect duplicate state variable reads
                    issues.extend(detect_duplicate_state_variable_read(function, file_path))

                    # Detect high Gas mathematical operations
                    issues.extend(detect_high_gas_math_operations(function, file_path))

                    # Detect redundant conditional checks
                    issues.extend(detect_redundant_condition_checks(function, file_path))

                    # Not using storage pointers
                    issues.extend(detect_unused_storage_pointer(function, file_path))

                    # Large memory array parameters
                    issues.extend(detect_large_memory_array(function, file_path))

        except Exception as e:
            traceback.print_exc()
            error_message = f"File analysis failed: {str(e)}"
            issues.append({
                "type": "Analysis error",
                "description": error_message,
                "location": Path(file_path).name
            })
    return issues
