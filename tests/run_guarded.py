"""Install permanent audit guard before loading owner controls; never run native code."""
import ctypes,runpy,sys
# Initialize Python standard-library ctypes before the permanent guard; all
# subsequent native lookup/call audit events from target code are denied.

def guard(event,args):
    if event.startswith(('subprocess.','socket.','ctypes.')) or event in {'os.system','os.exec','os.posix_spawn','os.fork','os.forkpty'}:
        raise RuntimeError('permanent inert-test guard: '+event)
sys.addaudithook(guard)
from pathlib import Path
sys.argv=[str(Path(__file__).with_name('test_smoke.py'))]
runpy.run_path(sys.argv[0],run_name='__main__')
