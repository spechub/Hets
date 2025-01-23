"""
Entry point for the Hets GUI application.

run: Runs the Hets GUI application.
"""


from .application import HetsApplication

def run():
    """
    Runs the Hets GUI application.

    Blocks until the application exits and exits the programm with the same status code.

    :return: None
    """
    import sys
    app = HetsApplication()
    exit_status = app.run(sys.argv)
    sys.exit(exit_status)
