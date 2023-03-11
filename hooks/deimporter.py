from fix_imports import *
import os
import pathlib
import utils

def list_files(startpath):
    """
    Recursively list all files in a directory and its subdirectories
    """
    for root, dirs, files in os.walk(startpath):
        dirs[:] = [d for d in dirs if os.path.join(root, d) != startpath]
        for file in files:
            if (os.path.dirname(os.path.join(root, file)) != startpath):
              # Print the fully qualified path of each file
              yield os.path.join(root, file)

agda_files = list(filter(lambda f: utils.isAgdaFile(pathlib.Path(f)), list_files("src")))


def deimportify(agda_file):
    # Now we need to find all imports, and then test one by one if they are used
    with open(agda_file, 'r', encoding='UTF-8') as file:
        contents = file.read()
        public, nonpublic, open_statements = fix_imports.get_imports(contents)

        if nonpublic is None:
            print(f"{str(i).rjust(len(str(len(agda_files))))} of {len(agda_files)}: Warning! Could not find imports in '{agda_file}'. Skipping.")

        print(nonpublic)
        pretty_imports_block = prettify_imports_to_block(block)

        new_content = contents[:start] + \
            pretty_imports_block + \
            contents[end:]
        
        with open(fpath, 'w') as file:
            file.write(new_content)



for i, agda_file in enumerate(agda_files):
    # If file doesn't compile, skip
    if (os.system("agda " + agda_file) != 0):
        print(f"{str(i).rjust(len(str(len(agda_files))))} of {len(agda_files)}: ERROR! File '{agda_file}' did not compile. Skipping.")

    # Now we need to find all imports, and then test one by one if they are used
    with open(agda_file, 'r', encoding='UTF-8') as file:
        contents = file.read()
        public, nonpublic, open_statements = get_imports(contents)

        if nonpublic is None:
            print(f"{str(i).rjust(len(str(len(agda_files))))} of {len(agda_files)}: Warning! Could not find imports in '{agda_file}'. Skipping.")

        print(nonpublic)

        newnonpublic = set(nonpublic)

        for statement in nonpublic:
            newnonpublic.discard(statement)
            prettify_imports_to_block(public, newnonpublic, open_statements)

            new_content = contents[:start] + \
              pretty_imports_block + \
              contents[end:]
            
            with open(agda_file, 'w') as file:
                file.write(new_content)
            
            if (os.system("agda " + agda_file) != 0):
                newnonpublic.add(statement)
            else: print(f"  the statement '{statement}' was unused in '{agda_file}'")


    print(f"{str(i).rjust(len(str(len(agda_files))))} of {len(agda_files)}: done with '{agda_file}'")