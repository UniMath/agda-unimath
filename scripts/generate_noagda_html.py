#!/usr/bin/env python3
# Run this script:
# $ ./scripts/generate_noagda_html.py outDir

import pathlib
import shutil
import sys
import utils

STATUS_FLAG_GIT_ERROR = 1
STATUS_OUT_NOT_DIR = 2

if __name__ == '__main__':
    status = 0
    root = 'src'
    outDir = pathlib.Path(sys.argv[1])

    try:
        git_tracked_files = set(utils.get_git_tracked_files())
    except subprocess.CalledProcessError:
        utils.eprint('Failed to get Git-tracked files')
        sys.exit(STATUS_FLAG_GIT_ERROR)

    try:
        outDir.mkdir(parents=True, exist_ok=True)
    except FileExistsError:
        utils.eprint('Output path exists and is not a directory')
        sys.exit(STATUS_OUT_NOT_DIR)

    for fpath in git_tracked_files:
        if fpath.parts[0] != root or not utils.is_agda_file(fpath):
            continue
        module_name = utils.get_agda_module_name(str(fpath), root)
        dest = outDir / (module_name + '.md')

        # Ideally we would try symlinks, but linkcheck always follows them and
        # then complains about links outside of the root directory
        shutil.copy(fpath, dest)

    sys.exit(status)
