# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html
import os.path
import sys


# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information
sys.path.insert(0, os.path.abspath("../src"))
print(sys.path)

project = 'Hets API'
copyright = '2023, Björn Gehrke'
author = 'Björn Gehrke'

release = '00.00.01'

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.viewcode',
    'sphinx.ext.napoleon',
    'sphinx.ext.autosummary'
]
autosummary_generate = True

templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']
html_show_sourcelink = False
html_copy_source = False

autodoc_mock_imports = ["hyphen", "hs"]
autodoc_typehints_format = "short"
autoclass_content = "both"

autodoc_default_options = {
    'exclude-members': 'hs_obj, hs_update'
}
