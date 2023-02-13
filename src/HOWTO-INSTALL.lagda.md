# INSTALL

Before you can use the `agda-unimath` library, you should have Agda installed on your machine and an editor that is compatible with Agda. We recommend `Emacs` and `VSCode`.

### Installation guides and tutorials for Agda

 - Go to the [installation guide](https://agda.readthedocs.io/en/latest/getting-started/installation.html) on the Agda documentation page for instructions to install Agda.
 - Once you have Agda up and running, you can copy our library to your machine using `git clone git@github.com:UniMath/agda-unimath.git`.
 - If you're new to Agda, see the [list of tutorials](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html) to learn how to use Agda.

### Setting up emacs for literate Agda files

The `agda-unimath` library is written in literate markdown agda. This means that all the files in the formalization have the extension `.lagda.md` and they consist of markdown text and `agda` code blocks. For your emacs to handle these files correctly, you need to add the following line to your `.emacs` file:

```md
(setq auto-mode-alist (cons '("\\.lagda.md$" . agda2-mode) auto-mode-alist))
```

### Setting up emacs for the notation of identity types

In the `agda-unimath` library, we use two notations for the identity type. The identity type is first introduced using Martin-Löf's original notation `Id`. Then we introduce as a secondary option the infix notation `_＝_`.

**Note**: The equals sign in the infix notation is not the standard equals sign on your keyboard, but it is the [full width equals sign](https://www.fileformat.info/info/unicode/char/ff1d/index.htm). Note that the full width equals sign is slightly wider, and it is highlighted in blue just like all the other defined constructions in Agda. In order to type the full width equals sign in Agda emacs mode, you need to add it to your Agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Click the `INS` button
- Type the regular equals sign `=` in the Key sequence field.
- Click the `INS` button
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the full width equals sign `＝`. While you're at it, you can also add the key sequence `yo` to obtain the Japanese symbol `ょ` for the Yoneda embedding.

### After the setup

With Agda installed and emacs correctly set up, you can start using the library. There is no need to install anything further. To compile the library, which is optional, run `make check` from the main folder of the repository. This generates the file `everything.lagda.md`, which imports all the files in the library and subsequently verifies them. You don't need to compile the entire library, however. You can simply open the file you're interested in and load it with Agda. This will verify the file and any prerequisites that are not already compiled.