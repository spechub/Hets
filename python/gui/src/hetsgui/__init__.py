
from .application import HetsApplication

def run():
    import sys
    app = HetsApplication()
    exit_status = app.run(sys.argv)
    sys.exit(exit_status)
