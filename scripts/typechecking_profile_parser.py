import json
import re
import os
import argparse
import csv


def parse_memory_profiling_data(filepath):
    results = dict()

    # Define patterns to match each line and their corresponding unit
    patterns = {
        "memory_allocated_in_heap": (r"(\d+(?:,\d+)*) bytes allocated in the heap", "B"),
        "memory_copied_during_GC": (r"(\d+(?:,\d+)*) bytes copied during GC", "B"),
        "maximum_residency": (r"(\d+(?:,\d+)*) bytes maximum residency", "B"),
        "memory_maximum_slop": (r"(\d+(?:,\d+)*) bytes maximum slop", "B"),
        "total_memory_in_use": (r"(\d+) MiB total memory in use", "MiB")
    }

    with open(filepath, 'r') as file:
        for line in file:
            for key, (pattern, unit) in patterns.items():
                match = re.search(pattern, line)
                if match:
                    value = int(match.group(1).replace(",", ""))
                    if key == "memory_maximum_slop":  # Convert maximum slo to KiB and truncate
                        value //= 1024
                        unit = "KiB"
                    elif unit == "B":  # Convert bytes to MiB and truncate
                        value //= 1024 * 1024
                        unit = "MiB"
                    results[key] = {"value": value, "unit": unit}

    return results

def parse_benchmark_results(input_path):
    benchmarks = dict()
    with open(input_path, 'r') as file:
        for line in file:
            # Match lines that end with "ms" indicating a timing result
            match = re.fullmatch(r'^\s*(\S+)\s+(\d+)(,\d+)*ms\s*$', line)
            if match:
                name = match.group(1).strip()
                # Correctly parse and combine the number groups to handle commas in numbers
                milliseconds = int("".join([x.replace(',', '') for x in match.groups()[1:] if x]))
                benchmarks[name] = {'value': milliseconds, 'unit':'ms'}
                # benchmarks.append({'name': name, 'value': milliseconds, 'unit':'ms'})
    return benchmarks

subdict =\
    lambda original_dict, keys_to_extract:\
        original_dict if keys_to_extract is None else {key: original_dict[key] for key in keys_to_extract if key in original_dict}


convert_dict_to_list =\
    lambda data, keys_to_extract=None: [{'name': name, **details} for name, details in subdict(data, keys_to_extract).items()]

def save_github_action_benchmark_json(output_path, benchmarks, memory_stats, benchmark_keys, memory_keys):
    with open(output_path, 'w') as file:
        json.dump(convert_dict_to_list(benchmarks, benchmark_keys) + convert_dict_to_list(memory_stats, memory_keys) , file, indent=2)


def read_existing_csv_to_dict(csv_path, commit_hash):
    # Initialize a dictionary to hold the CSV data
    data_dict = {}
    fieldnames = ['name', 'unit', commit_hash]

    # Check if the file exists and read its content
    if os.path.exists(csv_path):
        with open(csv_path, mode='r', newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            # Update fieldnames with those found in the existing CSV, plus the new commit hash if necessary
            fieldnames = reader.fieldnames + [commit_hash] if commit_hash not in reader.fieldnames else reader.fieldnames
            for row in reader:
                data_dict[row['name']] = row

    return data_dict, fieldnames

def update_csv_data(data_dict, benchmarks, memory_stats, commit_hash):
    # Combine benchmarks and memory stats for easier processing
    combined_data = {**memory_stats, **benchmarks}

    # Update the data_dict with new or updated values
    for name, details in combined_data.items():
        if name not in data_dict:
            data_dict[name] = {'name': name, 'unit': details['unit']}
        data_dict[name][commit_hash] = details['value']

def write_csv_from_dict(csv_path, data_dict, fieldnames, commit_hash):
    # Custom sort function: Sort by unit first, then capitalized names first, then alphabetical order
    custom_sort = lambda item: (item['unit'] == "ms", item['unit'] != "ms" or item['name'][0].islower(), 0 if item['unit'] != "ms" else -item[commit_hash])

    with open(csv_path, mode='w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        # Sort the data based on the custom sort function before writing
        sorted_data = sorted(data_dict.values(), key=custom_sort)
        for row in sorted_data:
            writer.writerow(row)

def save_as_csv(benchmarks, memory_stats, csv_path, commit_hash):
    data_dict, fieldnames = read_existing_csv_to_dict(csv_path, commit_hash)
    update_csv_data(data_dict, benchmarks, memory_stats, commit_hash)
    write_csv_from_dict(csv_path, data_dict, fieldnames, commit_hash)

if __name__ == "__main__":
    # Set up argument parsing
    parser = argparse.ArgumentParser(description='Convert benchmark results to JSON format.')
    parser.add_argument('input_times_path', help='Path to the input file containing typechecking times.')
    parser.add_argument('input_memory_path', help='Path to the input file containing memory statistics.')
    parser.add_argument('output_json_path', help='Path to the output JSON file.')
    parser.add_argument('csv_path', help='Path to the profiling CSV file.')
    parser.add_argument('commit_hash', help='Commit hash for current commit.')

    # Parse arguments from command line
    args = parser.parse_args()

    # Use the provided command-line arguments
    benchmarks = parse_benchmark_results(args.input_times_path)
    memory_stats = parse_memory_profiling_data(args.input_memory_path)

    save_github_action_benchmark_json(args.output_json_path, benchmarks, memory_stats, ["Total",], ["total_memory_in_use",])
    save_as_csv(benchmarks, memory_stats, args.csv_path, args.commit_hash)
