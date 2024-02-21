import json
import re
import argparse


def parse_memory_profiling_data(filepath):
    results = []

    # Define patterns to match each line and their corresponding unit
    patterns = {
        "bytes_allocated_in_heap": (r"(\d+(?:,\d+)*) bytes allocated in the heap", "bytes"),
        "bytes_copied_during_GC": (r"(\d+(?:,\d+)*) bytes copied during GC", "bytes"),
        "maximum_residency": (r"(\d+(?:,\d+)*) bytes maximum residency", "bytes"),
        "bytes_maximum_slop": (r"(\d+(?:,\d+)*) bytes maximum slop", "bytes"),
        "total_memory_in_use": (r"(\d+) MiB total memory in use", "MiB")
    }

    with open(filepath, 'r') as file:
        for line in file:
            for key, (pattern, unit) in patterns.items():
                match = re.search(pattern, line)
                if match:
                    value = int(match.group(1).replace(",", ""))
                    if unit == "bytes":  # Convert byts to MiB for consistency, if needed
                        value /= 1024 * 1024
                        unit = "MiB"
                    results.append({"name": key, "value": value, "unit": unit})

    return results

def parse_benchmark_results(input_path):
    benchmarks = []
    with open(input_path, 'r') as file:
        for line in file:
            # Match lines that end with "ms" indicating a timing result
            match = re.fullmatch(r'^\s*(\S+)\s+(\d+)(,\d+)*ms\s*$', line)
            if match:
                name = match.group(1).strip()
                # Correctly parse and combine the number groups to handle commas in numbers
                milliseconds = int("".join([x.replace(',', '') for x in match.groups()[1:] if x]))
                benchmarks.append({'name': name, 'value': milliseconds, 'unit':'ms'})
    return benchmarks

def save_as_json(benchmarks, memory_stats, output_path):
    with open(output_path, 'w') as file:
        json.dump(memory_stats + benchmarks, file, indent=2)

if __name__ == "__main__":
    # Set up argument parsing
    parser = argparse.ArgumentParser(description='Convert benchmark results to JSON format.')
    parser.add_argument('input_times_path', help='Path to the input file containing typechecking times.')
    parser.add_argument('input_memory_path', help='Path to the input file containing memory statistics.')
    parser.add_argument('output_path', help='Path to the output JSON file.')

    # Parse arguments from command line
    args = parser.parse_args()

    # Use the provided command-line arguments
    benchmarks = parse_benchmark_results(args.input_times_path)
    memory_stats = parse_memory_profiling_data(args.input_memory_path)

    save_as_json(benchmarks, memory_stats, args.output_path)
