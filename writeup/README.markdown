# The build process

There is a chewing-gum and duct-tape build process driving things for the moment.

All names NAME in Process_it_op.tbl are currently being macro expanded to \itop{REPLACEMENT}, where \itop is defined in pldi15.tex.
All names NAME in Process_tt_op.tbl are currently being macro expanded to \ttop{REPLACEMENT}, where \ttop is defined in pldi15.tex.
All names NAME in Process_*_macros.tbl are macro expanded to REPLACEMENT.

If a replacement is a literal '_' then REPLACEMENT is set to be NAME.

You can write
```raw
\some\latex\here
```
or
`\some\latex\here`{.raw}
to get literal latex into the document.

