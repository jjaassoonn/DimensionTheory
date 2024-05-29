(TeX-add-style-hook
 "print"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("hyperref" "unicode" "colorlinks=true" "linkcolor=blue" "urlcolor=magenta" "citecolor=blue") ("unicode-math" "warnings-off={mathtools-colon,mathtools-overbracket}")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "macros/common"
    "macros/print"
    "content"
    "article"
    "art10"
    "geometry"
    "expl3"
    "amssymb"
    "amsthm"
    "mathtools"
    "hyperref"
    "unicode-math"
    "thmtools"))
 :latex)

