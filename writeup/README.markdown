# The build process

There is a chewing-gum and duct-tape build process driving things for the moment.

All names NAME in Process_mathttNames.tbl are currently being macro expanded to \operatorname{\mathtt{NAME}}.
The line for this is Process:38 if you want to change it.

All names NAME in Process_mathitNames.tbl are currently being macro expanded to \mbox{\emph{NAME}}.
The line for this is Process:49 if you want to change it.

Process_macros.tbl is a list of [ NAME , REPLACEMENT, MODE ].
The Word mode will only match whole words, like "foo" in "foo bar" but not in "fooey".
The Anywehere mode is find/replace with no restrictions.

Another thought is to indirect these macros to latex, so mathtt name NAME goes to \mymathtt{NAME}.
