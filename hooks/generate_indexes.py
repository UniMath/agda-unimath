#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/generate_indexes.py fileName.lagda.md

# make a dict :
#   dict = { namespace : [files] }
# iterate src folder
#   get the dirs
#   for d in dirs:
#      fs = collect all the files
#      for f in fs:
#        dict


from collections import defaultdict
import os
import pathlib
import sys
import utils

status = 0
root = "src"


def get_subdirectories(startpath):
    for root, dirs, files in os.walk(startpath):
        for d in dirs:
            yield d

def get_files(path):
    return os.listdir(path)

def generate_title(namespace):
    return namespace.capitalize().replace("-"," ")

def generate_imports(namespace):
    namespace_path = os.path.join(root, namespace)
    namespace_files = filter(lambda f: utils.isAgdaFile(
        pathlib.Path(os.path.join(namespace_path, f)))
          , get_files(namespace_path))

    # 
    return "\n".join(sorted("open import " + namespace + "." + module_file[:module_file.index(".lagda.md")] + " public" for module_file in namespace_files))

template = \
'''# {title}

```agda
module {namespace} where

{imports}
```
'''

def generate_index(namespace):

    title = generate_title(namespace)
    imports = generate_imports(namespace)

    return template.format(title=title, namespace=namespace, imports=imports)

    
if __name__ == "__main__":
    namespaces = get_subdirectories(root)
    for namespace in namespaces:
        with open(os.path.join(root, namespace)+".lagda.md", "w") as namespace_file:
          namespace_file.write(generate_index(namespace))

    # with open(fpath, 'r', encoding='UTF-8') as file:
    #     contents = file.read()

  # sys.exit(status)
