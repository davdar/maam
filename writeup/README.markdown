# Building

First run 'make init'. This will set up a cabal sandbox and install pandoc into
it. If you want to nuke the cabal sandbox and start over run 'make reinit'.

After init, make should build the pdf without trouble. Let me know if you have
trouble.

# Using the build process

There is a chewing-gum and duct-tape build process driving things for the moment.

All of these things apply to pldi15.markdown as it gets turned into latex.

Inside code blocks:

- All names NAME in Process_it_op.tbl are currently being macro expanded to \itop{REPLACEMENT}, where \itop is defined in pldi15.tex.
- All names NAME in Process_tt_op.tbl are currently being macro expanded to \ttop{REPLACEMENT}, where \ttop is defined in pldi15.tex.
- All names NAME in Process_*_macros.tbl are macro expanded to REPLACEMENT.
- If a REPLACEMENT is a literal '_' then REPLACEMENT is set to be NAME.
- 'Word' mode will match 'foo' in 'foo bar' but not in 'fooey'.
- 'Anywhere' mode matches, well, anywhere.

Before latex processing:

Any line that starts with whitespace followed by '--' will be removed, like this one:
           -- a comment
-- also a comment

Outside code blocks:
- You can write tex inline like \some\latex\here.
  There is one caveot: if you open a \begin{env}, everything inside will be literal tex and won't use my macro replacement.
  You can get away from this by writing:
  ```raw
  \begin{env}
  ```
  or
  `\begin{env}`{.raw}
  to get literal latex into the document that won't gobble everything inside to
  be raw latex. You can also use this to typeset citations and references
  properly, i.e., Section`~\ref{introduction}`{.raw}
- Also, ", ---, -- and ... will automatically be converted to their tex
- counterparts ``, '', em-dash, en-dash, and elipses.
