# INSTALL

Before you can use the `agda-unimath` library, you should have Agda
installed on your machine. You can get Agda via following their
installation instructions, or using the provided Nix flake, if you're using Nix.
You should also have an editor capable of working with Agda file.
We recommend either of `Emacs` and `VSCode`.

### Installation guides

Get a copy of our library on your machine using
```shell
git clone git@github.com:UniMath/agda-unimath.git
```
then install Agda as described in the next section.

#### Without Nix

Go to the [installation guide](https://agda.readthedocs.io/en/latest/getting-started/installation.html) on the Agda documentation page for instructions to install Agda.

#### With Nix

The library comes with a development shell described in the flake.nix file. To activate the shell, open a terminal in the directory where you cloned the library, and run
```shell
nix develop
```
Then to make sure that your editor sees the Agda installation,
start it from within that shell, i.e. run `code` or `emacs` inside the shell.

To make `emacs` use the correct `agda2-mode` provided by the development environment,
add the following snippet to your `.emacs` file:
```elisp
(when (executable-find "agda-mode")
  (load-file (let ((coding-system-for-read 'utf-8))
               (shell-command-to-string "agda-mode locate"))))
```
which is a modified version of the usual agda2-mode setup provided by Agda,
except it checks if Agda is available, so that it doesn't cause errors
when opening Emacs outside the project.

### Setting up emacs for literate Agda files

The `agda-unimath` library is written in literate markdown agda. This means that all the files in the formalization have the extension `.lagda.md` and they consist of markdown text and `agda` code blocks. For your emacs to handle these files correctly, you need to add the following line to your `.emacs` file:

```elisp
(setq auto-mode-alist (cons '("\\.lagda.md$" . agda2-mode) auto-mode-alist))
```

### Tutorials for Agda

If you're new to Agda, see the [list of tutorials](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html) to learn how to use Agda.

### Setting up emacs for special symbols

In the `agda-unimath` library, we use two notations for the identity type. The identity type is first introduced using Martin-Löf's original notation `Id`. Then we introduce as a secondary option the infix notation `_＝_`.

**Note**: The equals sign in the infix notation is not the standard equals sign on your keyboard, but it is the [full width equals sign](https://www.fileformat.info/info/unicode/char/ff1d/index.htm). Note that the full width equals sign is slightly wider, and it is highlighted in blue just like all the other defined constructions in Agda. In order to type the full width equals sign in Agda emacs mode, you need to add it to your Agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Click the `INS` button
- Type the regular equals sign `=` in the Key sequence field.
- Click the `INS` button
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the
full width equals sign `＝`. While you're at it, you can also add the
key sequence `yo` to obtain the Japanese symbol `ょ` for the Yoneda
embedding.

### 80 character limit

The `agda-unimath` library maintains an 80 character limit
on the length of lines in the source code. This limit is to improve
readability, both in your programming environment and on our website.
Emacs has an option to display a line marking the 80th column.
This option can be enabled by adding

```elisp
(add-hook 'prog-mode-hook #'display-fill-column-indicator-mode)
```

to your `.emacs` file.

### Note on the library's use of unicode characters

This library makes extensive use of unicode characters.
It is therefore important to use a font family with wide
support for them.
For example, we make use of the
[middle dot](https://www.compart.com/en/unicode/U+00B7) symbol `·`,
as well as the [bullet operator](https://www.compart.com/en/unicode/U+2219) symbol `∙`, which in some fonts are indistinguishable. If these two symbols look the same in your editor, we suggest that you change your font.

As a suggestion, this website uses the following family of fonts in prioritized order (decreasing) to display Agda code:
```css
Menlo, Source Code Pro, Consolas, Monaco, Lucida Console, Liberation Mono, DejaVu Sans Mono, Bitstream Vera Sans Mono, Courier New, monospace
```

### After the setup

With Agda installed and emacs correctly set up, you can start using the library. There is no need to install anything further. To compile the library, which is optional, run `make check` from the main folder of the repository. This generates the file `everything.lagda.md`, which imports all the files in the library and subsequently verifies them. You don't need to compile the entire library, however. You can simply open the file you're interested in and load it with Agda. This will verify the file and any prerequisites that are not already compiled.

## Pre-commit hooks

The `agda-unimath` library comes with pre-commit hooks that checks
that files follow some basic formatting rules. To use these hooks,
you need to install the `pre-commit` tool. The easiest way to do
this is to use the Python package manager `pip`:

```shell
python3 -pip install pre-commit
```

Once you have installed `pre-commit`, next time before you open a new PR, please stage
all your changes and run the following command:

```shell
make pre-commit
```
