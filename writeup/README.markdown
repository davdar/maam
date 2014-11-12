# The build process

There is a chewing-gum and duct-tape build process driving things for the moment.

All names NAME in Process_mathttNames.tbl are currently being macro expanded to \operatorname{\mathtt{NAME}}.
The line for this is Process:38 if you want to change it.

All names NAME in Process_mathitNames.tbl are currently being macro expanded to \mbox{\emph{NAME}}.
The line for this is Process:49 if you want to change it.

Process_macros.tbl is a list of [ NAME , REPLACEMENT, MODE ].
The Word mode will only match whole words, like "foo" in "foo bar" but not in "fooey".
The Anywehere mode is find/replace with no restrictions.

Some macros are routed to \newcommand defined at the top of pldi15.tex.

A new feature!
Lines that start with \ like \begin{proposition} are preserved verbatim.
Processing is otherwise non-latex aware.

# QUIRKS

My hack for making "\begin{proposition}" show up as raw (not escaped) latex only works if there are no spaces on the line.
Therefore I'm processing the lines to replace '_' with ' '.
Example: 

markdown: \paragraph{A_Neat_Idea} 

will show up as

latex: \paragrapn{A Neat Idea}

and

markdown: \paragraph{A Neat Idea}

will show up as

latex: \paragraph{A Neat Idea \}

which is BAD
