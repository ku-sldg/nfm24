# Using This Template
1. Replace this readme with a description of the paper
2. Rename the file `samplepaper.tex` to something more meaningful
3. Replace `samplepaper` in the Makefile with your new paper name
4. Replace `samplepaper.pdf` in the `.gitignore` file so you don't end
   up checking in the built PDF file.
5. Edit the author section including emails, thanks, running header,
   and add orcid fields.	
6. Update the `bib` submodule and `sldg.bib` if needed by running
   `git submodule init` and `git submodule update`.
7. Descend into
   the `bib` directory and pull to get latest entries.  Push back to
   the lab repo if you add or edit entries.
8. Some includes are commented out as they are not always needed.
   Uncomment what you need and add others as needed. 
9. If you do not want to use `natbib` remove `\usepackage{natbib}`,
   add `\usepackage{cite}`, and swap `bibliographystyle` commands at
   the end of the document.
   
