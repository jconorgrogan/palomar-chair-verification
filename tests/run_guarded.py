#!/usr/bin/env python3
"""Permanent no-process/no-network guard, installed before loading reviewed helpers."""
import ctypes,sys
DENY=('subprocess.', 'os.system', 'os.exec', 'os.posix_spawn', 'os.spawn', 'os.fork', 'socket.', 'ctypes.')
def guard(event,args):
 if event.startswith(DENY):raise RuntimeError('inert guard forbids '+event)
sys.addaudithook(guard)
import runpy
from pathlib import Path
runpy.run_path(str(Path(__file__).with_name('test_pilot.py')),run_name='__main__')
