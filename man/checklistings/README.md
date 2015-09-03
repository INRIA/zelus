checklistings
=============

By [Timothy Bourke](http://www.tbrk.org)
and [Marc Pouzet](http://www.di.ens.fr/~pouzet).

User manuals and papers about programming languages usually contain many 
code samples, often with accompanying compiler messages giving the types 
of declarations or error messages explaining why certain declarations are 
invalid.

The `checklistings` package augments the
[fancyvrb](http://www.ctan.org/pkg/fancyvrb) and
[listings](http://www.ctan.org/pkg/listings) packages for including source
code in LaTeX documents with a way to pass the source code through a
compiler and also include the resulting messages in the document.

The motivation is to check the code samples in a document for syntax and
typing errors and to facilitate the inclusion of inferred types and compiler
warnings or errors in a text. This package is intentionally very lightweight
and unlike packages like [python](http://www.ctan.org/pkg/python) it is not
intended for interacting with an interpretor or including the execution
traces of code. While `checklistings` does not focus on a specific
programming language, it is designed to work well with ML-like languages.

Using the package involves three elements:

1. The declaration `\usepackage{checklistings}`.
2. The verbatim environment `\begin{chklisting}...\end{chklisting}`.
3. The shell script `checklistings.sh`.

In a first pass, `latex`/`pdflatex` outputs code samples into files.
The second pass is performed by `checklistings.sh` which passes each file
through a compiler to generate corresponding output files.
In a third pass, `latex`/`pdflatex` reads from the generated files to
incorporate the results into the document.

A `checklistings.hva` file is provided for interoperability with
[HeVeA](http://hevea.inria.fr).

The `checklistings` package may be distributed and/or modified under the
conditions of the
[LaTeX Project Public License](http://www.latex-project.org/lppl.txt),
either version 1.2 of this license or (at your option) any later version.

Please send comments, suggestions, and bug reports (with version number and
the keyword "checklistings" in the subject of the message) to
<tim@tbrk.org>. Please keep in mind that we prefer to keep `checklistings`
simple and lightweight rather than to incorporate many different
configuration and customization options.

This package was developed within the
[PARKAS](http://www.di.ens.fr/ParkasTeam.html) at
[Inria](http://www.inria.fr) and the [ENS](http://www.di.ens.fr).

