"""
This unit test checks the listenformessage() API call to make sure it can close
and then re-open a socket.
"""

#pragma repy

ds = listenformessage('127.0.0.1', 12345)
ts = listenforconnection('127.0.0.1', 12345)
ds.close()
ts.close()

