#!/usr/bin/env python

#    Chris Matthews - University of Victoria - July 2012

import sys
import os
import stat
import runonce

# We need lind_test_server.py, lind_fs_calls.py and lind_fs_constants.py.
# They should be in the REPY_PATH OR copy them in to this folder so python
# can import the lind_test_server

# add repy install path to script
repy_path = os.getenv("REPY_PATH")

if repy_path == None:
    # if not set, use the location of this file.
    (lind_fuse_path, name) = os.path.split(os.path.abspath(__file__))
    os.environ['REPY_PATH'] = lind_fuse_path
    code_path = lind_fuse_path
else:
    # If it is set, use the standard lind path
    code_path = os.path.join(repy_path, "repy/")

sys.path.append(code_path)



# change dir so the execfile in test server works
pwd = os.getcwd()
os.chdir(code_path)
import lind_test_server as lind
# and now back to where we started.
os.chdir(pwd)



import emulcomm
import emulfile
import emulmisc
import emultimer
import serialize
import time



metadatafilename = 'lind.metadata'

FILEDATAPREFIX = 'linddata.'

DIRECTORYPREFIX = 'D'

FILEPREFIX = 'F'

BLOCKSIZE = 4096 

MAXNOOFBLOCKS = 10000

MAXFILESIZE = 1638400 

MAXNOOFPOINTERININDEX = int(MAXFILESIZE / BLOCKSIZE)

MAXFREEPOINTERBLOCKS = int(MAXNOOFBLOCKS / MAXNOOFPOINTERININDEX)

ROOTDIRECTORYINODE = MAXFREEPOINTERBLOCKS + 1

UNASSIGNEDBLOCKPOINTER = -1

# delete constants
DELETE_INODEANDFREEUPBLOCK = 1
DELETE_FREEUPBLOCK = 2

# POINTER TYPE
DIRECT_POINTER = 0
INDIRECT_POINTER = 1

filesystemmetadata = {}

freeBlock = {}

superBlock = {}

dataBlocks = {}

# A lock that prevents inconsistencies in metadata
# filesystemmetadatalock = createlock()


# fast lookup table...   (Should I deprecate this?)
fastinodelookuptable = {}

# contains open file descriptor information... (keyed by fd)
filedescriptortable = {}

# contains file objects... (keyed by inode)
fileobjecttable = {}

# I use this so that I can assign to a global string (currentworkingdirectory)
# without using global, which is blocked by RepyV2
fs_calls_context = {}

# Where we currently are at...

fs_calls_context['currentworkingdirectory'] = '/'


def restore_metadata(metadatafilename):
  # should only be called with a fresh system...
  assert(filesystemmetadata == {})
  filesystemmetadata['freeBlock'] = {}
  filesystemmetadata['inodetable'] = {}

# sort the file based on their file names its good to restore in order
  files = [k for k in emulfile.listfiles() if FILEDATAPREFIX in k]
  files.sort(key = lambda x: int(x.split(".")[1]))
  for filename in files:

    # restore free blocks
    metadatafo = emulfile.emulated_open(filename,True)
    metadatastring = metadatafo.readat(None, 0)
    metadatafo.close()
    # restore only inode, directory, freeblock and superblock block others are just data blocks that we can ignore
    try:
      desiredmetadata = serialize.deserializedata(metadatastring)
      op = int(filename.split('.')[1])
      if op == 0:
        filesystemmetadata['superBlock'] = desiredmetadata
      elif op >=1 and op <= MAXFREEPOINTERBLOCKS:
        filesystemmetadata['freeBlock'][op] = desiredmetadata
      elif op > MAXFREEPOINTERBLOCKS:
        if 'location' in desiredmetadata or 'filename_to_inode_dict' in desiredmetadata:
          filesystemmetadata['inodetable'][op] = desiredmetadata
    except Exception:
      pass  
  _rebuild_fastinodelookuptable()

# I'm already added.
def _recursive_rebuild_fastinodelookuptable_helper(path, inode):
  
  # for each entry in my table...
  for entryname,entryinode in filesystemmetadata['inodetable'][inode]['filename_to_inode_dict'].iteritems():

    # ignore the initial F,D prefix
    entryname = entryname[1:]
    # if it's . or .. skip it.
    if entryname == '.' or entryname == '..':
      continue

    # always add it...
    entrypurepathname = _get_absolute_path(path+'/'+entryname)
    fastinodelookuptable[entrypurepathname] = entryinode

    # and recurse if a directory...
    if 'filename_to_inode_dict' in filesystemmetadata['inodetable'][entryinode]:
      _recursive_rebuild_fastinodelookuptable_helper(entrypurepathname,entryinode)
    

def _rebuild_fastinodelookuptable():
  # first, empty it...
  for item in fastinodelookuptable:
    del fastinodelookuptable[item]
  # now let's go through and add items...
  
  # I need to add the root.   
  fastinodelookuptable['/'] = ROOTDIRECTORYINODE
  # let's recursively do the rest...
  
  _recursive_rebuild_fastinodelookuptable_helper('/', ROOTDIRECTORYINODE)



# private helper function that converts a relative path or a path with things
# like foo/../bar to a normal path.
def _get_absolute_path(path):

  # should raise an ENOENT error...
  if path == '':
    return path

  # If it's a relative path, prepend the CWD...
  if path[0] != '/':
    path = fs_calls_context['currentworkingdirectory'] + '/' + path


  # now I'll split on '/'.   This gives a list like: ['','foo','bar'] for 
  # '/foo/bar'
  pathlist = path.split('/')

  # let's remove the leading ''
  assert(pathlist[0] == '')
  pathlist = pathlist[1:]

  # Now, let's remove any '.' entries...
  while True:
    try:
      pathlist.remove('.')
    except ValueError:
      break

  # Also remove any '' entries...
  while True:
    try:
      pathlist.remove('')
    except ValueError:
      break

  # NOTE: This makes '/foo/bar/' -> '/foo/bar'.   I think this is okay.
  
  # for a '..' entry, remove the previous entry (if one exists).   This will
  # only work if we go left to right.
  position = 0
  while position < len(pathlist):
    if pathlist[position] == '..':
      # if there is a parent, remove it and this entry.  
      if position > 0:
        del pathlist[position]
        del pathlist[position-1]

        # go back one position and continue...
        position = position -1
        continue

      else:
        # I'm at the beginning.   Remove this, but no need to adjust position
        del pathlist[position]
        continue

    else:
      # it's a normal entry...   move along...
      position = position + 1


  # now let's join the pathlist!
  return '/'+'/'.join(pathlist)


# private helper function
def _get_absolute_parent_path(path):
  return _get_absolute_path(path+'/..')
  
def _test_device_id():
  if filesystemmetadata['superBlock']['devId'] != 20:
    raise Exception("Wrong Device ID")

def _test_all_times_in_past():
  ts = int(time.time())

  # check filesystem creation time
  if filesystemmetadata['superBlock']['creationTime'] >= ts:
    raise Exception("Invalid FS creation time")
  for key, val in filesystemmetadata['inodetable'].iteritems():
    if 'filename_to_inode_dict' in val and ( val['atime'] >= ts or val['ctime'] >= ts or val['mtime'] >= ts ) :
      raise Exception("Directory inode :"+str(key)+" has invalid time [atime/ctime/mtime]")
    elif 'location' in val and ( val['atime'] >= ts or val['ctime'] >= ts or val['mtime'] >= ts ):
      raise Exception("File inode :"+str(key)+" has invalid time [atime/ctime/mtime]")

def _validate_free_blocks():
  number_of_blocks=0
  for key, val in filesystemmetadata['freeBlock'].iteritems():
    for k in val :
      if k != 'changed':
        number_of_blocks += 1
        if filesystemmetadata['freeBlock'][key][k] == False:
          try:
            fd = emulfile.emulated_open(FILEDATAPREFIX+str(k), False)
            fd.close()
          except Exception as e:
            raise Exception("Free Block pointing to a location that does not contain file")
        elif filesystemmetadata['freeBlock'][key][k] == True:
          try:
            fd = emulfile.emulated_open(FILEDATAPREFIX+str(k), False)
            fd.close()
            raise Exception("Free Block pointing to a location that contain a file")
          except Exception as e:
            pass

  if number_of_blocks != MAXNOOFBLOCKS:
      raise Exception("Free Blocks do not map to "+str(MAXNOOFBLOCKS)+" blocks")
    
def _validate_directory_pointers():
  for key, val in filesystemmetadata['inodetable'].iteritems():
    if 'filename_to_inode_dict' in val  :
      if DIRECTORYPREFIX+'.' not in val['filename_to_inode_dict'] or DIRECTORYPREFIX+'..' not in val['filename_to_inode_dict'] :
        raise Exception("Directory inode :"+str(key)+" does not contain either . or ..")

      dirLinks = [k for k in val['filename_to_inode_dict'] if DIRECTORYPREFIX in k ]
      linkcount = len(dirLinks)
      if filesystemmetadata['inodetable'][key]['linkcount'] != linkcount:
        raise Exception("Directory inode :"+str(key)+" linkcount mismatch")

def _validate_file_indirect():
  for key, val in filesystemmetadata['inodetable'].iteritems():
    if 'location' in val  :
      fd = emulfile.emulated_open(FILEDATAPREFIX+str(val['location']), False)
      try:
        data = serialize.deserializedata(fd.readat(None, 0))
      except Exception :
        if val['indirect'] == INDIRECT_POINTER:
          raise Exception("File inode :"+str(key)+" has indirect pointer set but index block missing")
        else:
          pass
      finally:
        fd.close()
      block_count =0
      if val['indirect'] == INDIRECT_POINTER:
        for k in data:
          if data[k] != -1:
            block_count += 1


      if val['size'] > 0 and val['indirect'] == DIRECT_POINTER and val['size'] > BLOCKSIZE:
        raise Exception("File inode :"+str(key)+" has indirect pointer set to 0 but file size exceeds block size")
      elif val['indirect'] == INDIRECT_POINTER and val['size'] > BLOCKSIZE*(block_count):
        raise Exception("File inode :"+str(key)+" has indirect pointer set to 1 but file size exceeds block size*number of blocks")
      elif val['indirect'] == INDIRECT_POINTER and val['size'] < BLOCKSIZE*(block_count)-1:
        raise Exception("File inode :"+str(key)+" has indirect pointer set to 1 but file size exceeds block size*number of blocks-1")


def main():
  restore_metadata(metadatafilename)

  try:
    _test_device_id()
  except Exception as e:
    print e

  try:
    _test_all_times_in_past()
  except Exception as e:
    print e

  try:
    _validate_free_blocks()
  except Exception as e:
    print e

  try:
    _validate_directory_pointers()
  except Exception as e:
    print e

  try:
    _validate_file_indirect()
  except Exception as e:
    print e


if __name__ == '__main__':
    main()
