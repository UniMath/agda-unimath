# Installing the library

## Overview

### Quick setup

To work or experiment with the agda-unimath library on your machine, you will
need to have Agda version 2.8.0 installed, and a suitable editor such as
[Emacs](https://www.gnu.org/software/emacs/) or
[Visual Studio Code](https://code.visualstudio.com/). The following instructions
will help you on your way right away:

1. [Getting a copy of the library](#getting-a-copy)
2. [Installing Agda](#installing-agda)
3. [Setting up your editor](#editor-setup)

### Setup for contributors

In order to contribute to the agda-unimath library you will additionally need:

1. `git`
2. `make`
3. `python` version 3.8 or newer
4. The python libraries `pre-commit`, `pybtex`, `requests`, `tomli`, and
   `graphviz`. These can be installed by running
   ```shell
   python3 -m pip install -r scripts/requirements.txt
   ```
5. `rust` version 1.68 or newer
6. `mdbook` version 4.34 or newer, along with the `catppuccin`, `katex`,
   `linkcheck`, and `pagetoc` plugins. These can be installed by running the
   command
   ```shell
   make install-website-dev
   ```
7. `graphviz`

All of these can also be installed in one go by using `nix`. In the section
[Creating a setup for contributors](#contributor-setup) we will walk you through
the steps of preparing your environment for contributing to the library with and
without `nix`.

Additionally, we added a [Troubleshooting](#troubleshooting) section at the end
of this guide. If you experience any issues during the setup process, don't
hesitate to reach out to us on the
[Univalent Agda discord server](https://discord.gg/Zp2e8hYsuX). Our community is
here to help and ensure you have a smooth experience.

## Getting a copy of the library {#getting-a-copy}

The way you install the library on your machine might depend on the way you plan
to use it. If you plan to contribute to the library, then we suggest first
creating a fork of the library, and then cloning your fork. If you don't intend
to contribute the library, then you don't need to create your own fork, and you
can proceed directly to clone the library.

### Creating a fork of the library

If your plan is to submit a contribution, or to do a project that eventually
could lead to a contribution to the library, then it is best to begin by
creating a fork of the library on GitHub:

1. Navigate to the library's GitHub page at
   [https://github.com/UniMath/agda-unimath](https://github.com/UniMath/agda-unimath).
2. In the upper-right corner of the page, click the "Fork" button.
3. Select your GitHub account to create the fork under.

### Cloning your fork of the library

After you have your own fork of the library, you can clone it to your machine
with git using the following command in your terminal:

```bash
git clone --depth 1 git@github.com:[YourUsername]/agda-unimath.git
```

Replace `[YourUsername]` with your actual GitHub username. This command will
clone a shallow copy of the library, i.e., a copy of the library without its
entire git history, which is a version of the library that is under 20MB in
size.

If you prefer to clone the library with its history, simply omit `--depth 1` in
the above command.

### Cloning the library directly

If you don't intend to contribute to the library, but still want to have a local
copy of it on your machine, you can clone it directly with

```bash
git clone --depth 1 git@github.com:UniMath/agda-unimath.git
```

This is not our first recommendation, however, because if you later decide to
use this clone for contributions, you will need some proficiency in using `git`
to adjust the remote addresses of your clone.

### Creating a branch within your clone of the library

Once you've cloned the library, we highly recommend you to preserve the `master`
branch in its original state and up to date with the official agda-unimath
repository. This means you should avoid making changes directly to the `master`
branch.

Instead, whenever you're about to start a new piece of work (be it a new
feature, bug fix, or any other modifications), create a new branch from
`master`. This way, you can keep track of different lines of work, isolate them
from each other, and prevent potential conflicts.

Here's a basic example of how you can create a new branch:

```bash
git checkout -b my-feature
```

This command creates a new branch named `my-feature` and automatically checks it
out, meaning your 'working directory' will switch to this branch.

By maintaining the `master` branch untouched, you ensure a clean, up-to-date
base that is aligned with the original library you forked from. This makes it
easier to pull in updates from the original repository and merge them into your
working branches when necessary.

## Installing Agda {#installing-agda}

The agda-unimath library is built and verified with Agda 2.8.0, and we provide
two methods for installation: with or without the package manager
[Nix](https://nixos.org/). Nix streamlines the installation of Agda and its
dependencies, providing a consistent and reproducible environment for the
library across different systems.

### Without Nix

To install Agda 2.8.0 without Nix, follow the
[installation guide](https://agda.readthedocs.io/en/latest/getting-started/installation.html)
provided on the Agda documentation page.

### With Nix

The library comes with a development shell described in the `flake.nix` file. To
activate the shell, open a terminal in the directory where you cloned the
library, and run:

```shell
nix develop
```

Once you've activated the shell, launch your editor from within it by running
`code` or `emacs`. This ensures your editor recognizes the Agda installation.

### Tutorials for Agda

If you're new to Agda, there are several resources available to help you learn
the basics and become proficient in using the language. We recommend starting
with the
[list of tutorials](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html)
provided on the Agda documentation page.

## Editor setup {#editor-setup}

We recommend either [Emacs](https://www.gnu.org/software/emacs/) or
[Visual Studio Code](https://code.visualstudio.com/) (VSCode) as your editor
when working with the agda-unimath library. Both editors offer support for Agda
development, and the choice between them is largely a matter of personal
preference. Below, you'll find setup instructions for each editor to help you
configure your preferred environment.

### Emacs

#### Agda mode using Nix

If you installed Agda using Nix, add the following snippet to your `.emacs` file
to use the correct `agda2-mode` provided by the development environment:

```elisp
(when (executable-find "agda-mode")
  (load-file (let ((coding-system-for-read 'utf-8))
               (shell-command-to-string "agda-mode locate"))))
```

This is a modified version of the usual `agda2-mode` setup provided by Agda,
except it checks if Agda is available, so that it doesn't cause errors when
opening Emacs outside the project.

#### Literate Agda files

The agda-unimath library is written in literate markdown Agda. Add the following
line to your `.emacs` file to enable Emacs to handle literate Agda files with
the `.lagda.md` extension:

```elisp
(setq auto-mode-alist (cons '("\\.lagda.md$" . agda2-mode) auto-mode-alist))
```

#### Special symbols

The agda-unimath library employs two notations for the identity type:
Martin-Löf's original notation `Id` and an infix notation `_＝_`. The infix
notation's equals sign is not the standard one, but rather the
[full width equals sign](https://codepoints.net/U+ff1d). Observe that the full
width equals sign is slightly wider, and is highlighted in blue just like all
the other defined constructions in Agda. To type the full width equals sign in
Agda's Emacs Mode, you need to add it to your Agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Press the `INS` key
- Type the regular equals sign `=` in the Key sequence field.
- Press the `INS` key
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the full
width equals sign `＝`. While you're at it, you can also add the key sequence
`yo` to obtain the Japanese symbol `ょ` for the Yoneda embedding.

#### 80-character limit

The agda-unimath library maintains an 80-character limit on the length of most
lines in the source code (see [CODINGSTYLE](CODINGSTYLE.md#character-limit) for
a list of exceptions). This limit is to improve readability, both in your
programming environment and on our website. To display a vertical ruler marking
the 80th column in Emacs, add:

```elisp
(add-hook 'prog-mode-hook #'display-fill-column-indicator-mode)
```

to your `.emacs` file.

### VSCode

The agda-unimath library comes with a predefined VSCode workspace. Open the
folder main repository folder in VSCode, and it should automatically recognize
the workspace and apply the appropriate settings.

#### Extensions

A collection of recommended extensions is included with the workspace to
streamline your experience while working with the library. These extensions
should be automatically suggested to you when you open the repository in VSCode.

##### Agda mode

One essential extension for interacting with Agda is
[`agda-mode`](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode).
After installing this extension, you'll be able to verify `.lagda.md` files by
opening them and using the `C-c C-l` command. For a full list of commands, see
the extension's reference page.

#### Special characters

The VSCode workspace adds snippets for inserting special symbols like `＝` and
`ょ`, since there's currently no way to add these to Agda's input mode in
VSCode.

To insert these symbols in the editor, follow these steps:

1. Begin typing one of the activation sequences listed below.
2. When the symbol appears as a greyed-out character in your editor, press `TAB`
   to insert it.

- `＝`: Type `Id`
- `ょ`: Type `yoneda`
- `⧄`: Type `diagonal` or `lifting`

These snippets are defined in `.vscode/agda.code-snippets`.

#### Autoformatting

For your convenience, the VSCode workspace configures several automatic
formatting functions. These functions continuously correct minor formatting
mistakes, ensuring a smoother coding experience.

### Note on the library's use of Unicode characters

This library relies heavily on Unicode characters, so it's important to use a
font family with comprehensive Unicode support in your editor. For instance, the
library utilizes the [middle dot](https://www.compart.com/en/unicode/U+00B7) `·`
and the [bullet operator](https://www.compart.com/en/unicode/U+2219) `∙`. In
some fonts, these two symbols appear identical. If you find it difficult to
distinguish between these symbols in your editor, we recommend switching to a
different font.

## After the setup

Congratulations! With Agda installed and your editor expertly configured, you're
now ready to dive into the library.

### Verifying the library

To verify a file and its prerequisites with Agda, simply open and load it. If
you want to compile the entire library, you can run `make check` from the
repository's main folder. This requires the
[GNU Make](https://www.gnu.org/software/make/) tool to be installed. The command
generates the `everything.lagda.md` file, which imports and verifies all files
in the library.

## Creating a setup for contributors {#contributor-setup}

We welcome and appreciate contributions from the community. If you're interested
in contributing to the agda-unimath library, you can follow the instructions
below to ensure a smooth setup and workflow. Also, please make sure to follow
our [coding style](CODINGSTYLE.md) and
[design principles](DESIGN-PRINCIPLES.md).

### Pre-commit hooks and Python dependencies {#pre-commit-hooks}

The agda-unimath library includes [pre-commit](https://pre-commit.com/) hooks
that enforce [basic formatting rules](CONTRIBUTING.md). These will inform you of
some rule violations in your commits, and for most violations they will also
automatically apply the required changes.

To utilize these hooks, if you did not install your environment using Nix, you
will need to install the `pre-commit` tool and the hooks' Python dependencies.
The easiest way to accomplish this is by using the Python package manager `pip`.

First, make sure that you have the latest version of Python and pip installed on
your computer; the hooks require Python 3.8 or newer. Then run the following
command from the repository's main folder:

```shell
python3 -m pip install -r scripts/requirements.txt
```

Note that Python keeps the installed dependencies separate for different Python
versions, so if you update Python, you need to re-run the above command.

Now, before you submit a Pull Request (PR) next time, you can run `pre-commit`
by staging your changes and executing the command `make pre-commit` from the
repository's main folder.

Keep in mind that `pre-commit` is also a part of the Continuous Integration
(CI), so any PR that violates the enforced conventions will be automatically
blocked from merging.

### Building and viewing the website locally {#build-website}

The build process for the website uses the
[Rust language](https://www.rust-lang.org/)'s package manager `cargo`. To
install Rust and `cargo`, follow
[their installation guide](https://doc.rust-lang.org/cargo/getting-started/installation.html).
After installation, proceed with the following steps to build and view the
website locally:

1. **Install website dependencies**: We've provided a `make` target that
   installs the website dependencies for you. In your terminal, run:

   ```shell
   make install-website-dev
   ```

   You only need to run this command once, unless the website's dependencies
   change.

2. **Build the website**: Once the dependencies are installed, you can build the
   website by running the following command:

   ```shell
   make website
   ```

3. **View the website locally**: After building the website, you can start the
   web server by running:

   ```shell
   make serve-website
   ```

   This may take a moment, but the website will be opened in your browser
   automatically if it succeeds.

You've now successfully set up the local environment for the website! As you
make changes to the website's source files, you can repeat steps 2 and 3 to view
the updates locally before pushing the changes to the repository.

## Troubleshooting {#troubleshooting}

If you encounter any issues during the installation process, don't hesitate to
reach out to us on the
[Univalent Agda discord server](https://discord.gg/Zp2e8hYsuX). Our community is
here to help and ensure you have a smooth experience.

### I have installed `make pre-commit` on my Debian-based system, but the `pre-commit` command isn't recognized. What should I do?

This issue can arise if the `pre-commit` executable gets placed in the
`~/.local/bin` directory, which might not be in your system's `PATH`.

**To resolve this:**

1. **Check the `~/.local/bin` directory**: Use the command
   `ls ~/.local/bin | grep pre-commit` to see if the executable is present.

2. **Update your `PATH`**:

   - If you're using the bash terminal, open your `.bashrc` file with a text
     editor like `nano`:

     ```bash
     nano ~/.bashrc
     ```

   - Add the following line to the end of the file:

     ```bash
     export PATH=$PATH:~/.local/bin
     ```

   - Save the file and close the editor.

3. **Reload your `.bashrc`**:

   - Run the following command to apply the changes:

     ```bash
     source ~/.bashrc
     ```

Now, try running the `pre-commit` command again. It should be recognized.
