# Use xelatex
$pdf_mode = 5;

# Run bibtex or biber whenever it appears necessary to update the bbl files
# without checking for the existence of the bib files
# i.e. presume whatever it's compiling has access to the bib file.
# This means they will get deleted in a cleanup.
 $bibtex_use = 2;

# Clean up some extra latex bits
$clean_full_ext = 'listing lol';


# Tell it what the main file is
@default_files = ('17377693.tex');
