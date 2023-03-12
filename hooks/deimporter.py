from fix_imports import *
import itertools
import os
import pathlib
import subprocess
import utils

def get_files(startpath):
    """
    Recursively list all files in a directory and its subdirectories
    """
    for root, dirs, files in os.walk(startpath):
        dirs[:] = [d for d in dirs if os.path.join(root, d) != startpath]
        for file in files:
            # Yield the fully qualified path of each file
            yield os.path.join(root, file)

def get_files(path):
    """
    Recursively list all files in a directory and its subdirectories
    """
    return os.listdir(path)

if __name__ == "__main__":

  agda_files = filter(lambda f: utils.isAgdaFile(pathlib.Path(f)) and os.path.dirname(f) != "src", get_files("src"))
  
  for i, agda_file in enumerate(agda_files):
      # If file doesn't compile, skip
      print(f"{str(i+1).rjust(len(str(len(agda_files))))} of {len(agda_files)}: '{agda_file}'", end="")

      # Now we need to find all imports, and then test one by one if they are used
      with open(agda_file, 'r', encoding='UTF-8') as file:
          contents = file.read()
          block, start, end = get_imports_block(contents)
          public, nonpublic, open_statements = categorize_imports(block)

          if nonpublic is None:
              print(f" Warning! Could not find imports. Skipping.")
              continue
          elif (subprocess.call("agda " + agda_file, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0):
              print(f" ERROR! did not compile. Skipping.")
              continue
          else: print(" typechecked.")


          newnonpublic = set(nonpublic)

          for statement in nonpublic:
              newnonpublic.discard(statement)
              pretty_imports_block = prettify_imports_to_block(public, newnonpublic, open_statements)

              new_content = contents[:start] + \
                pretty_imports_block + \
                contents[end:]

              with open(agda_file, 'w') as file:
                  file.write(new_content)

              if (subprocess.call("agda " + agda_file, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0):
                  newnonpublic.add(statement)
              else: print(f"  the statement '{statement}' was unused")

          # Write final version
          pretty_imports_block = prettify_imports_to_block(public, newnonpublic, open_statements)

          new_content = contents[:start] + \
            pretty_imports_block + \
            contents[end:]

          with open(agda_file, 'w') as file:
              file.write(new_content)

# Check if we can demote a foundation import to a foundation-core import
if __name__ == "__main__":
  foundation_files = filter(lambda f: utils.isAgdaFile(pathlib.Path(f)), itertools.chain(get_files("src/foundation"), get_files("src/foundation-core")))

  for agda_file in foundation_files:
      print(f"{str(i+1).rjust(len(str(len(agda_files))))} of {len(agda_files)}: '{agda_file}'", end="")

      with open(agda_file, 'r', encoding='UTF-8') as file:
          contents = file.read()
          block, start, end = get_imports_block(contents)
          public, nonpublic, open_statements = categorize_imports(block)

          if nonpublic is None:
              print(f" Warning! Could not find imports. Skipping.")
              continue
          elif (subprocess.call("agda " + agda_file, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0):
              print(f" ERROR! did not compile. Skipping.")
              continue
          else: print(" typechecked.")

          newnonpublic = set(nonpublic)

          # Subdivide imports into namespaces
          namespaces = subdivide_namespaces_imports(nonpublic)

          if not "foundation" in namespaces.keys():
              print("No foundation imports. Done.")
              continue

          for statement in namespaces["foundation"]:
              newnonpublic.discard("open import " + statement)
              newnonpublic.add("open import " + statement.replace("foundation.", "foundation-core."))
              pretty_imports_block = prettify_imports_to_block(public, newnonpublic, open_statements)

              new_content = contents[:start] + \
                pretty_imports_block + \
                contents[end:]

              with open(agda_file, 'w') as file:
                  file.write(new_content)

              if (subprocess.call("agda " + agda_file, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0):
                  newnonpublic.discard("open import " + statement.replace("foundation.", "foundation-core."))
                  newnonpublic.add("open import " + statement)
              else: print(f"  the module '{statement}' could be imported from core instead")

          # Write final version
          pretty_imports_block = prettify_imports_to_block(public, newnonpublic, open_statements)

          new_content = contents[:start] + \
            pretty_imports_block + \
            contents[end:]

          with open(agda_file, 'w') as file:
              file.write(new_content)
