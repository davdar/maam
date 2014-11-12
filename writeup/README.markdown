# The build process

There is a chewing-gum and duct-tape build process driving things for the moment.

All names NAME in Process_it_op.tbl are currently being macro expanded to \itop{REPLACEMENT}, where \itop is defined in pldi15.tex.
All names NAME in Process_tt_op.tbl are currently being macro expanded to \ttop{REPLACEMENT}, where \ttop is defined in pldi15.tex.
All names NAME in Process_*_macros.tbl are macro expanded to REPLACEMENT.

If a replacement is a literal '_' then REPLACEMENT is set to be NAME.

You can write tex inline like \some\latex\here.
There is one caveot: if you open a \begin{env}, everything inside will be literal tex and won't use my macro replacement.
You can get away from this by writing:
```raw
\begin{env}
```
or
`\begin{env}`{.raw}
to get literal latex into the document that won't gobble everything inside to be raw latex.


