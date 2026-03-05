#!/usr/bin/env python3
"""
Convert VRPLC instances from custom format to MiniZinc DZN format.

Pattern discovered:
- Scale factor: 23 (all time values divided by 23)
- T_dzn = 150 (= T_orig / 23)
- V = P (vehicles = pickups)
- P = R / 2 (half of requests are pickups)
- a, b, s = original values / 23 (using round for safety)
- q: first P values unchanged (positive), last P values negated (deliveries)
- l: location index extracted from "L-X" -> X
- time matrix: ceil(euclidean_distance / 23) between locations
"""

import math
import os
import glob
import re


def parse_original_format(content):
    """Parse the original format file content."""
    lines = content.strip().split('\n')

    data = {}
    locations = {}  # Will store (X, Y) for each location index (0=depot)
    requests = []   # Will store (L, A, B, S, Q) for each request

    section = None

    for line in lines:
        line = line.strip()
        if not line or line.startswith('#'):
            continue

        # Parse key-value pairs like "T: 3450"
        if ':' in line and not line.startswith('R-') and not line.startswith('L-'):
            parts = line.split(':', 1)
            if len(parts) == 2:
                key = parts[0].strip()
                value = parts[1].strip()
                if key == 'InstanceName':
                    data[key] = value
                elif key in ['T', 'R', 'Q', 'C']:
                    data[key] = int(value)
            continue

        # Detect section headers by checking column names
        parts = line.split()
        if len(parts) >= 3 and parts[0] == 'L' and parts[1] == 'X' and parts[2] == 'Y':
            section = 'locations'
            continue
        if len(parts) >= 6 and parts[0] == 'R' and parts[1] == 'L':
            section = 'requests'
            continue

        # Parse location data: "L-D 0 0" or "L-1 -299 253"
        if section == 'locations' and line.startswith('L-'):
            parts = line.split()
            if len(parts) >= 3:
                loc_name = parts[0]
                x = int(parts[1])
                y = int(parts[2])
                if loc_name == 'L-D':
                    locations[0] = (x, y)  # Depot is location 0
                else:
                    loc_idx = int(loc_name.replace('L-', ''))
                    locations[loc_idx] = (x, y)

        # Parse request data: "R-1 L-1 414 1196 322 1"
        elif section == 'requests' and line.startswith('R-'):
            parts = line.split()
            if len(parts) >= 6:
                loc_str = parts[1]
                loc_idx = int(loc_str.replace('L-', ''))
                a = int(parts[2])
                b = int(parts[3])
                s = int(parts[4])
                q = int(parts[5])
                requests.append((loc_idx, a, b, s, q))

    return data, locations, requests


def compute_distance(x1, y1, x2, y2):
    """Compute Euclidean distance between two points."""
    return math.sqrt((x2 - x1)**2 + (y2 - y1)**2)


def generate_dzn(data, locations, requests):
    """Generate the DZN format output."""

    SCALE = 23  # Scaling factor

    R = data['R']
    P = R // 2          # Number of pickups (= number of pickup-delivery pairs)
    V = P               # Number of vehicles equals number of pickups
    T = 150             # Scaled time horizon (3450 / 23)
    Q = data['Q']       # Vehicle capacity (unchanged)
    C = data['C']       # Location capacity (unchanged)
    L = max(k for k in locations.keys() if k > 0)  # Number of locations (excluding depot)

    # Total nodes: R requests + V start nodes + V end nodes
    N = R + 2 * V

    # Build l array (location index for each request, 1-indexed)
    l_array = [requests[i][0] for i in range(R)]

    # Build a, b, s arrays (time values scaled by 23)
    # Use round() for safety, though values should divide evenly
    a_array = [round(requests[i][1] / SCALE) for i in range(R)]
    b_array = [round(requests[i][2] / SCALE) for i in range(R)]
    s_array = [round(requests[i][3] / SCALE) for i in range(R)]

    # Build q array: pickups positive, deliveries negative
    q_array = []
    for i in range(R):
        if i < P:
            # Pickup: keep positive
            q_array.append(requests[i][4])
        else:
            # Delivery: negate the value
            q_array.append(-requests[i][4])

    # Build time matrix
    # Node locations:
    #   - Nodes 1..R are requests, using their l value as location
    #   - Nodes R+1..R+V are start nodes (at depot, location 0)
    #   - Nodes R+V+1..N are end nodes (at depot, location 0)
    node_locations = []
    for i in range(R):
        node_locations.append(l_array[i])
    for i in range(2 * V):  # Start and end nodes at depot
        node_locations.append(0)

    # Compute time matrix with ceiling of scaled Euclidean distance
    time_matrix = []
    for i in range(N):
        row = []
        loc_i = node_locations[i]
        x_i, y_i = locations[loc_i]
        for j in range(N):
            loc_j = node_locations[j]
            x_j, y_j = locations[loc_j]
            dist = compute_distance(x_i, y_i, x_j, y_j)
            scaled_dist = math.ceil(dist / SCALE)
            row.append(scaled_dist)
        time_matrix.append(row)

    # Format output
    output_lines = []
    output_lines.append(f"T = {T};")
    output_lines.append(f"V = {V};")
    output_lines.append(f"Q = {Q};")
    output_lines.append(f"L = {L};")
    output_lines.append(f"C = {C};")
    output_lines.append(f"P = {P};")

    # Format time matrix as MiniZinc 2D array literal
    time_lines = []
    for i, row in enumerate(time_matrix):
        row_str = ",".join(f"{v:3d}" for v in row)
        if i == 0:
            # First row on same line as opening bracket
            time_lines.append(f"time = [|{row_str},")
        elif i < N - 1:
            time_lines.append(f"        |{row_str},")
        else:
            time_lines.append(f"        |{row_str}|];")
    output_lines.append("\n".join(time_lines))

    # Format 1D arrays
    def format_array(name, arr):
        values = ",".join(f"{v:3d}" for v in arr)
        return f"{name} =     [{values}];"

    output_lines.append(format_array("l", l_array))
    output_lines.append(format_array("a", a_array))
    output_lines.append(format_array("b", b_array))
    output_lines.append(format_array("s", s_array))
    output_lines.append(format_array("q", q_array))

    return "\n".join(output_lines)


def convert_file(input_path, output_path):
    """Convert a single file from original format to DZN format."""
    with open(input_path, 'r') as f:
        content = f.read()

    data, locations, requests = parse_original_format(content)

    # Validate parsed data
    if 'R' not in data:
        raise ValueError(f"Missing 'R' parameter in {input_path}")
    if len(requests) != data['R']:
        raise ValueError(f"Expected {data['R']} requests, found {len(requests)} in {input_path}")
    if 0 not in locations:
        raise ValueError(f"Missing depot (L-D) in {input_path}")

    dzn_content = generate_dzn(data, locations, requests)

    with open(output_path, 'w') as f:
        f.write(dzn_content)
        f.write("\n")

    print(f"Converted: {input_path} -> {output_path}")
    return True


def main():
    """Convert all .txt files in current directory to .dzn files."""
    txt_files = glob.glob("*.txt")

    if not txt_files:
        print("No .txt files found in current directory.")
        print("Usage: Place .txt files with VRPLC instances in the current directory and run this script.")
        return

    success_count = 0
    error_count = 0

    for txt_file in sorted(txt_files):
        dzn_file = os.path.splitext(txt_file)[0] + '.dzn'
        try:
            if convert_file(txt_file, dzn_file):
                success_count += 1
        except Exception as e:
            print(f"Error converting {txt_file}: {e}")
            error_count += 1

    print(f"\nConversion complete: {success_count} succeeded, {error_count} failed")


if __name__ == "__main__":
    main()
