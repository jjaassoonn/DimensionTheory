(TeX-add-style-hook
 "web"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("blueprint" "showmore" "dep_graph")))
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
    "macros/web"
    "content"
    "article"
    "art10"
    "amssymb"
    "amsthm"
    "amsmath"
    "hyperref"
    "blueprint"))
 :latex)

