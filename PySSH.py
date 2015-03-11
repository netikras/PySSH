#!/usr/bin/env python 

'''
Script is meant to be used as a library. 
What it does is simply embedding 'ssh' command and auto-logging in.

Once logged-in user can:
	* run custom commands on a remote server;
	* run a locally stored script [it will be run line-by-line so no need to escape metachars, etc.]
	* got to interactive mode. User will get direct access to remote shell (with some bugs as 'TAB' keypress, etc.)
	* enter commands Interpreter mode 
	
'''

import errno
import os, sys
import pwd
import socket
import struct
#try:
#	import ssl
#except:
#	self._debug("ssl library not found")
import termios
import select
import signal
import socket
#import thread
from threading import Thread
import fcntl
import time
import pty
import inspect ## for stack traces
from subprocess import Popen, PIPE


STDIN_FILENO  = 0
STDOUT_FILENO = 1
STDERR_FILENO = 2

NAMEPIPE  = [
			STDIN_FILENO,
			STDOUT_FILENO,
			STDERR_FILENO
			]
			
RMT_NAMEPIPE  = [
				-1,
				-1,
				-1
				]

STDINS  = [STDIN_FILENO ]
STDOUTS = [STDOUT_FILENO]
STDDBGS = [STDOUT_FILENO]

STDINS_pending  = []
STDOUTS_pending = []
STDDBGS_pending = []


CHILD   = 0

__all__ = ['ssh', 'Keys']


def _getFunctionName(stack_depth=1):
	return inspect.stack()[stack_depth][3]


class ssh:
	
	__all__ = [	'_debug', '_pollPID', '_processIsRunning', '_unblockPipes', '_startReader', '_prepareShell', 'setAltPipes', 
				'attach', 'sendAttachData', 'assignLogFile', 'setHost', 'setUsername', 'setPasswords', 'setPort', 'setSSHpath', 
				'debugMode', 'TrapSignals', 'spawnSSH', 'getTTYsize', 'setTTYsize', 'adaptTTYsize', 'close', 'autoLogin', 
				'authenticateAltSTDIN', 'openListeningSocket', 'getLine', 'Write', 'sendLine', 'interact', 'sendScript', 
				'interpreterMap2', 'ping']
	
	def __init__(self, host='', user='', psws=[], port=''):
		
		##_____ login info _____#
		self.host = host		# remote host we will connect to
		self.port = port		# ssh port
		self.user = user		# user we will be using to access remote host via ssh
		if len(psws) == 0: ## if none passwords were given
			self.psws = []		#-- not sure I need this..
			self.pswd = ""		# so we have no default password
		else:
			self.psws = psws	# possible ssh passwords
			self.pswd = psws[0] # a correct ssh password
		#-------------------#
			

		
		## [0]name,[1]passwd,[2]uid,[3]gid,[4]gecos,[5]homedir,[6]shell
		self.USER = pwd.getpwuid(os.getuid())
		self.HOST = socket.gethostname()
		
		if not self.user:    self.user = self.USER[0]
		if not self.port:    self.port = 22
		if not self.host:    self.host = self.HOST
		

		
		
		##________ Socket info ____________##
		self.socket_connections_MAX = 5		#
		self.socket_port = 12347			#
		self.socket_ip   = self.HOST		#
		self.socket_lsn	 = None				#
		self.socket_actv = None				#
		self.sockets_list= {}				## contents: {socket:[rmt_ip, rmt_port, active=True/False], ...}
		#self.socket_context = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
		#-----------------------------------#
		
		
		
		##_________ Attach() related ______________##
		#self.attach_passphrase      = self.psws[0]	# Passphrase to allow writing to stdin
		self.attach_HANDLER			= None
		self.attach_passphrase      = self.pswd		# Passphrase to allow writing to stdin
		self.a_fd_expiry_timeout    = 60			# Timeut value after which -rw will be disabled
		self.allowed_client_users   = [self.USER[0]]#
		self.attached_clients		= {}			# {fd : [name, host, -rw(True/False)]}
		self.client_attached_rw_msg = "=== Client attached -rw ===\n"
		self.alt_pipes_dir    		= os.environ['HOME'] + '/'
		self.attach_nodes_BASE		= os.environ['HOME']
		self.attach_nodes			= {}			# {"NodeName":[stdin, stdout, listenerThread], ... }
		#-------------------------------------------#
		
		
		self.ssh_path         = '/usr/bin/ssh'
		self.shell_prompt     = "PySSH:[\u@\h] \w \$ "              ## Basic
		self.ssh_params       = (
								"PySSH",
								"-o", "UserKnownHostsFile=/dev/null",
								"-o", "StrictHostKeyChecking=no",
								#"-o", "ConnectTimeout=5",
								"-e", "~",
								"-p", self.port,
								"-l", self.user,
								"-q",
								self.host
								)
		self.shell_prompt_alt = "[\D{%g%m%d %H:%M:%S}]\u@\h:\w \$ " ## with date and time
		self.testLine         = "f6bc67cf79b34613e8bf36abdeae19e2"  ## some dummy line
		self.prompts          = {
							'bash':'PySSH:[\u@\h] \w \$ ',
							'ksh' :'PySSH[%s@%s] \$ ' % (self.user, self.host),
							'orig':''
								}
		self.OS = {}

		self.change_PS1       = True
		self.pid			  = 0
		self.tc_orig_settings = termios.tcgetattr(0)
		
		#_________ CI related __________#
		self.CI_header		  = ""		#
		self.CI_HISTORY		  = [""]	#
		self.CI_H_length	  = 0		#
		self.CI_H_position	  = 0		#
		#-------------------------------#
		
		##__________ TIMEOUTS __________#
		self.TIMEOUT_login       = 30	## How long will the script wait until we're authenticated
		self.TIMEOUT_command     = 20	## How long will the script wait until response to command is received
		#self.TIMEOUT_inactivity  = 600	## How long we'll be waiting for input before kicking off
		self.TIMEOUT_select_read = 30	#
		#-------------------------------#
		
		self.SIG_CLOSE = 1 ## When closing -- send HUP to actual SSH session
		
		self.readBufferSize = 1024
		self.stdin_echo_enabled = False		## Setting STDIN terminal ECHO mode
		self.remote_echo_enabled = False	## Setting REMOTE terminal ECHO mode
		
		#___________ FLAGS _____________#
		self.F_LOGGEDIN       = False	## A flag which is set to TRUE once we've got confirmation we're in the server
		self.F_QUIET          = False	#
		self.F_PAUSEREADER    = False	## Flag will cause to pause READER thread
		self.F_HANDLEALTPIPES = False	#
		self.F_CLIENTMODE     = False	#
		self.F_RMTCLIENT      = False	## controlling connection via socket
		self.F_LOGGED         = False	#
		self.F_CLOSING        = False   #
		self.F_SECURESOCK     = True	# ## Using ssl/tls
		#-------------------------------#
		
		self.LOGfile = {'path':None, 'fd':None}

		
		self.mute = False		## Will suppress output to terminal here and there
		self.READY = False
		
		self.DEBUG_LEVEL = 1	## DEBUG depth.
		self.debug_levels = {	## DEBUG message flags mapped to DEBUG levels
							' '   :0, 
							'CRIT':1, 
							'ERR' :2,
							'WARN':3, 
							'INFO':4
							}	
		
		self.key = Keys()			## Some keyboard keys meanings are saved in this object in HEX
		self.F = TextFormat
		#signal.signal(signal.SIGINT, self._interruptHandler)
		
	
	
	

	
	def TrapSignals(self):
		signal.signal(signal.SIGALRM,  self._sig_handler)
		signal.signal(signal.SIGWINCH, self._sig_handler)
		signal.signal(signal.SIGCHLD,  self._sig_handler)
	
	
	def _sig_handler(self, signum, stack=None):
		if signum == signal.SIGALRM:
			self._debug("________INTERRUPT: ALARM!_________")
			pass
				
		elif signum == signal.SIGWINCH:
			self._debug("________INTERRUPT: WINCH!_________")
			#os.kill(self.pid, signum) ## sending winch to ssh session
			self.adaptTTYsize()
			
		elif signum == signal.SIGCHLD:
			self._debug("________INTERRUPT: CHLD!__________")
			proc_stat = self._pollPID()
			if proc_stat > 0:
				self._debug("Child exited with code: %s" % str(proc_stat))
				self.F_LOGGEDIN = False
			elif proc_stat < 0:
				self._debug("Child exited due to signal: %s" % str(proc_stat))
				self.F_LOGGEDIN = False
			elif self._processIsRunning(): 
				self._debug("CHILD process (%s) sent an interruption although it's still running and no signal has hit it" % str(self.pid) )
			else:
				self._debug("Child exited with code: 0")
				self.F_LOGGEDIN = False
				
			if not self.F_LOGGEDIN:
				
				self._unblockPipes(RMT_NAMEPIPE + NAMEPIPE, to_send=' ')

	
	def _pollPID(self, pid=None):
		if not pid: pid = self.pid ## Most likely we'll be looking for child PID (actual SSH session)
		try:
			ret_pid, ret_status = os.waitpid(pid, os.WNOHANG)
			
			if ret_pid == pid:
				if os.WIFSIGNALED(ret_status):
					## died on a signal?
					self._debug("SIGNALLED", "WARN")
					return -os.WTERMSIG(ret_status)
				elif os.WIFEXITED(ret_status):
					self._debug("EXITTED", "WARN")
					return os.WEXITSTATUS(ret_status)
				else:
					self._debug("Not really sure what's wrong.. Child has returned hell knows what: '(%s, %s)'" % (ret_pid, ret_status), "WARN")
				
			else:
				## Child did not return anything
				pass
		except Exception, e: self._debug("Exception while polling child PID: '%s'" % str(e))
		return 0
		
	
		
	def _processIsRunning(self, pid=None):
		if not pid: pid = self.pid ## Most likely we'll be looking for child PID (actual SSH session)
		try:
			os.kill(pid, 0)
			self._debug("PID: %s is running" % str(pid))
			return True

		except: 
			self._debug("PID: %s is NOT running" % str(pid))
		return False
		
	
	
	def ping(self, host=None, reply_timeout = 2, packet_count = 1, path_to_ping = "/bin/ping"):
		""" Uses native ping tool to ping the host. Returns touple: (ReturnCode, STDOUT, STDERR) """
		if not host: host = self.host
		
		null = open(os.devnull, 'wb')
		pinger = Popen([path_to_ping, "-q", "-W", str(reply_timeout), "-c", str(packet_count), host], stdout=PIPE, stderr=PIPE)
		out, err = pinger.communicate()
		null.close()
		self._debug("Ping to '%s' status:" % (host))
		self._debug("STDOUT: %s" % out)
		if err: self._debug("STDERR: %s" % err, "CRIT")
		return (pinger.returncode, out, err )
	
	
	
	
	
	def _socket_reading_thread(self,sock=None, addr=None):

		if not sock:
			self._debug("Cannot start reading from remote socket - none given", "ERR")
			return -1
		
			
		
		self.sockets_list[sock] = [addr[0], addr[1], True]

		pipe_STDINr, pipe_STDINw = os.pipe()
		pipe_STDOUTr, pipe_STDOUTw = os.pipe()

		STDINS.append(pipe_STDINr)
		STDOUTS.append(pipe_STDOUTw)
		#STDINS_pending.append(pipe_STDIN)


		while self.sockets_list[sock][-1]:
			
			r,w,x = select.select([sock.fileno()] + [pipe_STDOUTr],[],[],self.TIMEOUT_select_read)
			
			if not r: continue
			
			try:
				'''
				print "Unlocked:"
				print r
				print "SOCKET:"
				print sock.fileno()
				print "STDOUTS:"
				print STDOUTS
				#'''

				if r[0] == pipe_STDOUTr: ## there's something to read from STDOUT
					stdout_data=os.read(r[0], self.readBufferSize)
					sock.send(stdout_data)
					
				elif r[0] in [sock.fileno()]:
					rcvd = sock.recv(self.readBufferSize)
					
					if not rcvd:
						# close the socket
						self._debug("Socket closed")
						self.sockets_list[sock][-1] = False

					try:
						os.write(pipe_STDINw, rcvd) # piping stuff to STDINS
					except Exception, ex:
						self._debug("WRITE EXCEPTION: '%s'" % ex, "ERR")

				
				else: 
					self._debug("ELSE kicked in.. could not find '%s' in '%s' or '%s'" % (r[0], STDOUTS, [sock.fileno()]) , "ERR")
					continue
			except Exception, ex:
				self._debug("SOCK_READER EXCEPTION: '%s'" % ex, "ERR")
				continue
			
		self._debug("socket's ACTIVE flag has changed to False so connection dropped", "WARN")
		
		
		
		sock.close()
		self.sockets_list.pop(sock, None)	## removing socket from active connections list
		STDOUTS.remove(pipe_STDOUTw)		## removing stdout pipe from STDOUTS
		
		try:
			STDINS_pending.remove(pipe_STDINr)	# removing stdin pipe from STDINS_pending list
		except:
			pass
		try:
			STDINS.remove(pipe_STDINr)			# removing stdin pipe from STDINS list
		except:
			pass
		try:
			self._debug("sending NULL message to stdins pipes to release the lock")
			os.write(pipe_STDINw, '')
			#self.Write(STDINS + STDINS_pending, '')
			
		except Exception, ex:
			self._debug(" sending NULL might have failed... see here: '%s'" % s)
		
		os.close(pipe_STDINw )				## closing all the pipes
		os.close(pipe_STDOUTw)				## closing all the pipes
		os.close(pipe_STDINr )				## closing all the pipes
		os.close(pipe_STDOUTr)				## closing all the pipes
		self._debug("---LEAVING SOCKET READER THREAD---", "WARN")
		return
		
	
	
	def _socket_listening_thread(self):
		if not self.socket_lsn:
			self._debug("Cannot start listening for socket -- none was passed", "ERR")
			return -1
			
			
			
			
		while self.F_RMTCLIENT:
			try:
				self._debug("Accept()'ing -- waiting for new connections")
				(sock_conn, addr) = self.socket_lsn.accept()
				
				#if self.F_SECURESOCK:
				#	sock_conn = self.socket_context.wrap_socket(sock_conn, server_side=True)
				
				self._debug("ACCEPTED: conn: '%s', addr:'%s'" % (sock_conn, addr))
				reader = Thread(target=self._socket_reading_thread, args=(sock_conn, addr))
				reader.start()
				
			except Exception, ex:
				print "EXCEPT_SOCKET: '%s'" % ex
				continue
		
		
		self.socket_lsn.settimeout(1)		
		self.socket_lsn.close()
		self.socket_lsn = None
		
		self._debug("---LEAVING SOCKET LISTENER THREAD---", "WARN")
		self._debug(self.socket_lsn)	
		return
	
	
	
	def openListeningSocket(self):
		self._debug("")
		if not self.socket_port:
			self._debug("You must set 'socket_port' before opening a socket", "ERR")
			return -1
		try:
			self._debug("Creating a listener socket")
			self.socket_lsn = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
			self._debug("Binding to '%s:%d'" % (self.socket_ip, self.socket_port))
			self.socket_lsn.bind((self.socket_ip, self.socket_port))
			self._debug("Setting socket to LISTEN mode. Enabling BLOCKING")
			self.socket_lsn.listen(self.socket_connections_MAX)
			self.socket_lsn.setblocking(1)
			#self.socket_lsn.settimeout(self.TIMEOUT_select_read)
			
			self.F_RMTCLIENT = True
			self._debug("Stating listener thread")
			listener = Thread(target=self._socket_listening_thread)
			listener.start()
		except Exception, ex:
			self._debug("Could not create a socket: '%s'" % ex, "ERR")
		pass
		
	
	
	
	def authenticateAltSTDIN(self, line=None, fd=None, separ='\n', cnt=3):
		"""
		method will decide whether received string is a proper request for authentication
		to get -rw permissions to STDIN
		#"""
		if not line or not fd:
			self._debug("method needs both: line read and fd.", "ERR")
			return False
			
		authenticated = False
		try:
			
			if line.count(separ) == cnt:
				line = line.split(separ)
				
				pw   = line[0]
				name = line[1]
				host = line[2]
				
				if      pw == self.attach_passphrase \
					and name in self.allowed_client_users:
						
					self.attached_clients[fd] = [name, host, True]
					authenticated = True
					self._debug("Client attached -rw successfully: '%s'" % self.attached_clients)
					STDINS.append(fd)
		except Exception, ex:
			self._debug("exception... could not obtain all data required for authentication")
			
		return authenticated
	

	class _altPipesHandlerT(Thread):
		############################
		## Thread runs separately and 
		##   handles alternative pipes.
		##   This includes authenticating 
		##   and disabling attached clients
		############################
		
		def __init__(self, SSH):
			Thread.__init__(self)
			self.SSH = SSH	## PARENT -- i.e. MAIN SSH thread
			
			self.waiting_for_username = False
			self.SSH.F_HANDLEALTPIPES = True
			self.F_RUNNING			  = True
			
			self.readTimeout 	= 30
			self.inputFDs 		= []
			self.activeFD		= 0

			self.SSH._debug("Starting alt_pipes_handler thread")
		
		
		
		def run(self):
			
			line 		= ""
			BUFFER		= ""
			requestedFD	= []
			waiting_for_username = False
			
			while self.SSH.F_HANDLEALTPIPES and self.F_RUNNING:
				try:
					requestedFD = select.select(self.inputFDs, [],[], self.readTimeout)
				except Exception, ex:
					self.SSH._debug("Could not select() on client READ fd: '%s'" % ex, 'WARN')

					while not len(self.inputFDs):
						time.sleep(3)
					continue

				if requestedFD[0]: ## if it's not a timeout
					requestedFD = requestedFD[0][0] ## get the first fd available on a list

					#if requestedFD not in STDINS: ## if it is a potential request to attach
												## if not - do not steal data!
					if requestedFD != self.activeFD:
						try: ## read for a passphrase...
							#line = os.read(requestedFD, self.SSH.readBufferSize)
							line = self.SSH.getLine([requestedFD], self.readTimeout, self.SSH.readBufferSize) ## timeout of 30 secs

						except Exception, ex:
							self.SSH._debug("Could not read() from client: '%s'" % ex, 'WARN')
							
						if line[-1] == '\n': ## Assuming someone is trying to authenticate to the pipe. '\n' has to be sent last separatelly after entering auth data
						#if line == '\n': ## Assuming someone is trying to authenticate to the pipe. '\n' has to be sent last separatelly after entering auth data
							line = line[:-1] ## Removind the trailing '\n'
							
							## Auth. data:
							## 		session password\n
							## 		username\n
							## 		host user is authenticating from\n
							
							## Logging to the session automatically, i.e. with PySSH libs
							if self.authenticate(requestedFD, BUFFER):
							
								self.activateFD(requestedFD, activate=True)
								
								
								self.SSH.Write(STDOUTS, "\n=== %s@%s attached in -rw mode ===\n" % (\
													self.SSH.attached_clients[requestedFD][0], \
													self.SSH.attached_clients[requestedFD][1])\
													)
							
							
							
							## Logging to the session manually
							## !! DISABLED !! Use echo -ne "sess_pw\nusername\nhostname\n instead"
							#elif waiting_for_username and (BUFFER != '') and (BUFFER in self.SSH.allowed_client_users):
							#	STDINS.append(requestedFD)
							#	self.SSH.Write(STDOUTS, "\n=== %s attached in -rw mode ===\n" % BUFFER)
							#	waiting_for_username = False
							#elif BUFFER == self.SSH.attach_passphrase: ## checking if correct password has been entered
							#	waiting_for_username = True
								
								
							BUFFER=''
							
						else: 
							BUFFER += line
								
				else: ## TIMEOUT -- time to set fd to INACTIVE if it was active before
					self.SSH._debug("TIMEOUT while select()ing alt fds")
					#if inpFD in STDINS:
					#	self._debug("Client WRITE fd expired after inactivity timeout: '%d'. fd='%s'" % (self.a_fd_expiry_timeout, inpFD))
					#	STDINS.remove(inpFD)
					#	self.attached_clients[inpFD][2] = False
					#	STDINS_pending.append(inpFD)
					self.activateFD(activate=False)
					BUFFER=''
						
			self.SSH._debug("---LEAVING ALT_FD_HANDLER THREAD---")
			return
			
			
		def activateFD(self, newFD=None, activate=True):
			#########################
			## Activate user on a FD
			#########################
			try:
				self.SSH._debug("DEactivating alt_fd: %s" % str(self.activeFD))
				self.SSH.attached_clients[self.activeFD][2] = False
				STDINS.remove(self.activeFD)
				STDINS_pending.remove(self.activeFD)
			except Exception, e:
				pass
			
			if activate and newFD:
				self.activeFD = newFD
				self.SSH._debug("Activating new alt_fd: %s" % str(self.activeFD))
				
				self.SSH.attached_clients[ newFD ][2] = True
				STDINS_pending.append(newFD)
				STDINS.append(newFD)
			else:
				self.activeFD = 0
		
		
		def addPipe(self, newPipe):
			#########################
			## Add a new pipe to STDINS_pending
			#########################
			if not newPipe in self.inputFDs:
				self.SSH._debug("Adding new alt_pipe: %d" % newPipe)
				self.inputFDs.append(newPipe)
				STDINS_pending.append(newPipe)
				self.SSH._unblockPipes(self.inputFDs) ## adding new pipe to select()
			pass
		
		
		def remPipe(self, oldPipe):
			#########################
			## Remove a pipe from 
			## STDINS_pending/STDINS
			#########################
			if oldPipe in self.inputFDs:
				self.SSH._debug("Removing alt_fd: %d" % oldPipe)
				self.inputFDs.remove(oldPipe)
				if oldPipe in STDINS_pending: STDINS_pending.remove(oldPipe)
				if oldPipe in STDINS: STDINS.remove(oldPipe)
		
			
			
		def authenticate(self, stdin_fd, authLine, separ='\n', cnt=3):
			#########################
			## There should be two lines separated by '\n':
			##	1) username
			##	2) attach() password
			#########################
			
			self.SSH._debug("Authenticating FD: %s" % str(stdin_fd))
			
			if not (authLine and stdin_fd):
				self.SSH._debug("method needs both: line read and #fd.", "ERR")
				return False
			
			authenticated = False
			try:
				
				if authLine.count(separ) == cnt:
					authLine = authLine.split(separ)
					pw   = authLine[0]
					name = authLine[1]
					host = authLine[2]
					if (pw == self.SSH.attach_passphrase) and (name in self.SSH.allowed_client_users):
						self.SSH.attached_clients[stdin_fd] = [name, host, True]
						authenticated = True
						self.SSH._debug("Client attached -rw successfully: '%s'" % self.SSH.attached_clients)
						STDINS.append(stdin_fd)
			except Exception, ex:
				self.SSH._debug("exception... could not obtain all data required for authentication")
				
			return authenticated
			
			
		def LEAVE(self):
			#########################
			## Exit this thread
			#########################
			self.SSH._debug("Leaving Alt Pipes Reader Thread", "WARN")
			self.readTimeout	= 0
			self.F_RUNNING 		= False
			self.SSH._unblockPipes(self.inputFDs + STDINS_pending, to_send=' ')
	
	
	def _altPipesHandlerThread(self, inpFD, outpFD):
		"""
		Thread will run in bg and listen for any activity going on
		alternate input pipes.
		By default -ro permissions are set. To enable -rw mode
		a client must enter a correct passphrase 
		#"""

		
		BUFFER = ''
		line   = ''
		waiting_for_username = False
		self.F_HANDLEALTPIPES = True

		self._debug("Starting alt_pipes_handler for FD: %s" % inpFD)
		while self.F_HANDLEALTPIPES: 

			
			try:
				requested = select.select([inpFD], [],[], self.a_fd_expiry_timeout)
			except Exception, ex:
				self._debug("Could not select() on client READ fd: '%s'" % ex, 'WARN')

			if requested[0]: ## if it's not a timeout
				requested = requested[0][0] ## get the first fd available on a list

				if requested not in STDINS: ## if it is a potential request to attach
											## if not - do not steal data!
					try: ## read for a passphrase...
						line = os.read(requested, self.readBufferSize)
					except Exception, ex:
						self._debug("Could not read() from client: '%s'" % ex, 'WARN')
						
					if line == '\n': 
						#print BUFFER
						## Logging to the session automatically
						if self.authenticateAltSTDIN(BUFFER, requested):
							
							self.Write(STDOUTS, "\n=== %s@%s attached in -rw mode ===\n" % (\
												self.attached_clients[requested][0], \
												self.attached_clients[requested][1])\
												)
						
						
						
						## Logging to the session manually
						elif waiting_for_username and BUFFER != '' and BUFFER in self.allowed_client_users:
							STDINS.append(requested)
							self.Write(STDOUTS, "\n=== %s attached in -rw mode ===\n" % BUFFER)
							waiting_for_username = False
						elif BUFFER == self.attach_passphrase: ## checking if correct password has been entered
							waiting_for_username = True
							
							
						BUFFER=''
						
					else: 
						BUFFER += line
							
			else: ## TIMEOUT -- time to set fd to INACTIVE if it was active before
				self._debug("TIMEOUT while select()ing alt fds")
				if inpFD in STDINS:
					self._debug("Client WRITE fd expired after inactivity timeout: '%d'. fd='%s'" % (self.a_fd_expiry_timeout, inpFD))
					STDINS.remove(inpFD)
					self.attached_clients[inpFD][2] = False
					STDINS_pending.append(inpFD)
					BUFFER=''
					
		self._debug("---LEAVING ALT_FD_HANDLER THREAD---")
		return

	
	
	def addAltNode(self, stdin='stdin', stdout='stdout', nodeName=None):
		""" Method sets another set of pipes for communication with the child process.
		Paths of those pipes are passed as strings.
		Once pipes are set data streams are good to flow through them.
		
		WARNING! by default this method will open a pipe file to redirect streams.
				Pipes have limited buffer size. This means that if pipe is only
				filled and never read the buffer will fill-up and pause the
				PySSH i/o flow until pipe is flushed. To see pipe size run:
				M=0; while :; do dd if=/dev/zero bs=1k count=1 2>/dev/null; M=$[$M+1]; echo -en "\r$M KB" 1>&2; done | sleep 999
		"""
		
		
		if nodeName == None: nodeName = "Node"
		
		if nodeName in self.attach_nodes:
			indx=1
			temp_name = nodeName + str(indx)
			while temp_name in self.attach_nodes:
				temp_name = nodeName + str(indx)
			nodeName = temp_name

		
		#self.attach_nodes[nodeName] = [stdin, stdout]
		
		if stdin  == 'stdin' : stdin  = self.attach_nodes_BASE + '/' + nodeName + '/' + stdin
		if stdout == 'stdout': stdout = self.attach_nodes_BASE + '/' + nodeName + '/' + stdout
		
		if not os.path.exists(self.attach_nodes_BASE): 
			os.mkdir(self.attach_nodes_BASE)
		if not os.path.exists(self.attach_nodes_BASE + '/' + nodeName): 
			os.mkdir(self.attach_nodes_BASE + '/' + nodeName)
		
		if not os.path.exists(stdin):  os.mkfifo(stdin , 0222) ## --w--w--w-
		if not os.path.exists(stdout): os.mkfifo(stdout, 0444) ## -r--r--r--
		
		
		"""
		stdouts should be available to READ by other clients as they 
		should be all logged anyway...
		STDINs should be only available to access with a passphrase.
		#"""
		
		#STDINS.append ( os.open(stdin , os.O_RDWR) )
		
		pend_inp = os.open(stdin , os.O_RDWR)
		outp     = os.open(stdout, os.O_RDWR)
		
		self._debug("appending alternative stdout: fd='%d'" % outp)
		STDOUTS.append( outp )
		#STDDBGS.append( os.open(debug , os.O_RDWR) )
		
		STDINS_pending.append ( pend_inp )
		
		
		
		self.attached_clients[pend_inp] = [None, None, False]
		
		alt_pipes_listener = Thread(target=self._altPipesHandlerThread, 
									args=(pend_inp, outp),
									name=nodeName)
		
		self.attach_nodes[nodeName] = [stdin, stdout, pend_inp, outp]
		#self.attach_nodes[nodeName].append(alt_pipes_listener)

		#alt_pipes_listener.start()
		try:
			if not self.attach_HANDLER:
				self.attach_HANDLER = self._altPipesHandlerT(self)
				self.attach_HANDLER.start()
			self.attach_HANDLER.addPipe(pend_inp)
		except Exception, e: print e
	
	def removeAltNode(self, nodeName=None):
		if not nodeName: return -1
		
		try:
			try: details = self.attach_nodes[nodeName]
			except Exception, e: os.write(NAMEPIPE[1], "E: Cannot find node: '%s'\n" % (nodeName))
			del self.attach_nodes[nodeName]
			del self.attached_clients[details[2]]
			
			try: self.attach_HANDLER.remPipe(details[2])
			except Exception, e: print e;pass
			
			try: STDOUTS.remove(details[3])
			except Exception, e: print e;pass
			
			try: os.close(details[2])
			except Exception, e: print e;pass
			
			try: os.close(details[3])
			except Exception, e: print e;pass
			
			try: os.unlink(details[0])
			except Exception, e: print e;pass
			
			try: os.unlink(details[1])
			except Exception, e: print e;pass
			
			try: os.rmdir(self.attach_nodes_BASE + '/' + nodeName)
			except Exception, e: os.write(NAMEPIPE[1], "E: Cannot remove directory '%s': ['%s']\n" % (nodeName, e));pass
		
		except Exception, e: print e
		
		
	""" #def attach(self, pid=0):
	def attach(self, stdin='/dev/null', stdout='/dev/null', debug='/dev/null',mode='ro', pid=0):
	
		self.F_CLIENTMODE = True
		
		if mode == 'no':
			self.CI_header = "Local session"
			if len(STDIN_FILENO ) == 1:
				os.close(STDIN_FILENO[0] )
			if len(STDOUT_FILENO) == 1:
				os.close(STDOUT_FILENO[0])
			STDINS  = [STDIN_FILENO ]
			STDOUTS = [STDOUT_FILENO]
			STDDBGS = [STDOUT_FILENO]
			if self.parent_fd:
				RMT_NAMEPIPE[0] = self.parent_fd
				RMT_NAMEPIPE[1] = self.parent_fd
			else:
				self._debug("You are not session leader - there are no child processes running", "WARN")
			return
		
		
		self.CI_header = "CLIENT session"
		
		self.pid    = pid
	
		RMT_NAMEPIPE[0] = os.open(stdin , os.O_RDWR|os.O_APPEND)    ## Parent's stdin we'll send data to
		RMT_NAMEPIPE[1] = os.open(stdout, os.O_RDWR)              ## Parent's stdout we'll have to capture
		
		self._enableCannonical(NAMEPIPE[0], True)
		self._enableEcho(NAMEPIPE[0], False)
		
		try: 
			STDINS  = [ NAMEPIPE[0]                           ]
			STDOUTS = [ os.open('/dev/null', os.O_RDWR)       ]
			STDDBGS = [ os.open(debug, os.O_RDWR|os.O_APPEND) ]
		except Exception, ex:
			self._debug("Could not open alternate FDs. Error: '%s'" % ex, "CRIT")
			return -1
		
		self.F_LOGGEDIN = True
		self._startReader()
		
		if mode == 'rw':
			if self.attach_passphrase:
				self.sendAttachData(self.attach_passphrase)
			else:
				print "Attaching in -rw mode requires a session passphrase"
		
	#"""
	
	def attach(self, pathToNode=""):
		
		if os.path.exists(pathToNode):
			try:
				stdin  = os.open(pathToNode + "/stdin" , os.O_RDWR, os.O_APPEND)
				stdout = os.open(pathToNode + "/stdout", os.O_RDWR)
				
				RMT_NAMEPIPE[0] = stdin
				RMT_NAMEPIPE[1] = stdout
				
				self._enableCannonical(NAMEPIPE[0], True)
				self._enableEcho(NAMEPIPE[0], False)
				
				try: 
					STDINS  = [ NAMEPIPE[0]                           ]
					STDOUTS = [ os.open('/dev/null', os.O_RDWR)       ]
					STDDBGS = [ os.open(debug, os.O_RDWR|os.O_APPEND) ]
				except Exception, ex:
					self._debug("Could not open alternate FDs. Error: '%s'" % ex, "CRIT")
					return -1
				
				
				self.F_CLIENTMODE = True
				self.CI_header = "CLIENT session"
				self.pid=0
				self._startReader()
				
				if self.attach_passphrase:
					self.sendAttachData(self.attach_passphrase)
				else:
					print "Attaching in -rw mode requires a session passphrase"
				
			except: pass
	
	
	def sendAttachData(self, pw):
		"""
		Method sends data required to attached in -rw mode.
		#"""
		if not self.F_CLIENTMODE:
			self._debug("You're not in CLIENT mode. What are you attaching to..?", "WARN")
			return -1
		self._debug("Sending attach() credentials: %s, %s, %s" % ("password", self.USER[0], self.HOST))
		self.Write([RMT_NAMEPIPE[0]], pw			+ '\n' 
									+ self.USER[0] 	+ '\n' 
									+ self.HOST 	+ '\n' )
		
	
	
	def assignLogFile(self, filePath=None):
		## Cannot accept FDs as these might interfere with local open FDs. It would get messy...
		if filePath:
			try:
				self._debug("Assigning log file: '%s'" % filePath)
				
				self.LOGfile['fd'] = os.open(filePath, os.O_RDWR | os.O_APPEND | os.O_CREAT)
				self.LOGfile['path'] = filePath
				self._debug("appending logfile fd '%d' to STDOUTS" % self.LOGfile['fd'])
				STDOUTS.append(self.LOGfile['fd'])
				self.F_LOGGED = True
				return 0
			except Exception, ex:
				self._debug("Cannot open log file: '%s'" % filePath, "ERR")
				return -1
		else:
			self._debug("Cannot find FILE PATH for logging %s" % filePath, "ERR")
			return -1
			
	
	
	def setHost(self, host=None):
		if host:
			self.host = host
		return self.host
		
	def setUsername(self, username=None):
		if username:
			self.user = username
		return self.user
		
	def setPasswords(self, pw=[None]):
		if not len(pw) == 0 and pw[0]:
			self.psws = pw
		return self.psws
		
	def setPort(self, port=None):
		if port:
			self.port = port
		return self.port
		
	def setSSHpath(self, path=None):
		if path:
			self.ssh_path = path
		return self.ssh_path
	
	
	
	
	
	## DEBUG related methods ##
	def debugMode(self, level = 1):
		""" Method sets debug mode from 0 to 4, where 0 is the quietest and 4 is the noisiest """
		if level < 5:
			self.DEBUG_LEVEL = level
			self._debug("Changing DEBUG depth to %d" % level)
			return
		self._debug("Cannot set DEBUG depth to '%d'. Values [0;4] are available only" % level, "WARN")
	
	
	#_debug = lambda line,severity, self=self:  self.DEBUG_LEVEL and self.__debug(line, severity) 
	
	def _debug(self, line="", severity="INFO"):
		""" Function prints debug information to stdout if debugMode is set to >0 """
		#if self.DEBUG_LEVEL and self.debug_levels[severity] <= self.DEBUG_LEVEL:
		if self.debug_levels[severity] <= self.DEBUG_LEVEL:
			separ = "::"
			prefix="{%s()}%s" % (_getFunctionName(stack_depth=2), separ)
			try:
				self.Write(STDDBGS, "DEBUG[%d]%s %s %s %s\n" % (os.getpid(),prefix, severity, separ, line))
			except Exception, ex:
				pass
	
	
	
	## Connection birth and death related methods ##
	def spawnSSH(self):
		""" Method opens a TTY and fork-execs a ssh connection on it """
		## Opening terminal and saving pipe ends
		if self.F_CLIENTMODE:
			self._debug("Cannot spawn SSH connection when running in CLIENT mode. This is not how it works...", 'ERR')
			return -1
			
		self._debug("Opening PTY")
		self.parent_fd, self.child_fd = os.openpty();
		

		if self.parent_fd < 0 or self.child_fd < 0:
			errmsg="parent_fd == %d and child_fd == %d" % (self.parent_fd, self.child_fd)
			self._debug(errmsg, "ERR")
			raise OSError("ERR[%s()] :: %s" % (_getFunctionName(),errmsg))
			
		self._debug("Fork'ing")
		self.pid = os.fork()
		
		
		if self.pid == CHILD: ## from pty lib, means 0
			self._debug("Just discovered that I'm a CHILD with PID: %d" % os.getpid())
			os.close(self.parent_fd)
			## Copying terminal settings from host TTY to the forked one. We will execute ssh here.
			termios.tcsetattr(self.child_fd, termios.TCSANOW, termios.tcgetattr(0))
		
			## Setting child as the head of whole terminal system
			self._debug("Setting child as the head of the TTY (and session as well)")
			self._setControllingTTY(self.child_fd)
			
			#oldflags = fcntl.fcntl(self.child_fd, fcntl.F_GETFL)
			#fcntl.fcntl(self.child_fd, fcntl.F_SETFL, oldflags | os.O_NONBLOCK)
			
			self._debug("dup2()'ing FDs")
			os.dup2( self.child_fd, NAMEPIPE[0] )
			os.dup2( self.child_fd, NAMEPIPE[1] )
			os.dup2( self.child_fd, NAMEPIPE[2] )
			
			try:
				self._debug("Exec-ing: 'execvpe(%s, %s)'" % (self.ssh_path, self.ssh_params))
				os.execvpe(self.ssh_path, self.ssh_params, os.environ)
			except Exception, e:
				self._debug("Cannot exec: %s" % e, "CRIT")
			
			print "AFTER-EXEC life -- application must NEVER reach this point. If you see this message - there's something very wrong..."
			self._debug("AFTER-EXEC life -- application must NEVER reach this point. If you see this message - there's something very wrong...", "CRIT")
			os.exit(1)
			
		else: # // PARENT 
			os.waitpid(self.pid, os.WNOHANG)
			try:
				RMT_NAMEPIPE[0] = self.parent_fd
				RMT_NAMEPIPE[1] = self.parent_fd
				RMT_NAMEPIPE[2] = self.parent_fd
				self._debug("I'm a parent so I'm closing child_fd")
				#os.close(self.child_fd)
			except Exception,e:
				self._debug("Cannot close child_fd: %s" % e, "ERR")
			
			self.TrapSignals()
			return self.pid, self.parent_fd

	def _setControllingTTY(self, tty_fd):
		""" Private method that gives session control to child process running ssh """
		if self.F_CLIENTMODE:
			return -1
			
			
		child_name = os.ttyname(tty_fd)
		
		## Opening /dev/tty will drop us from controlling tty with O_NOCTTY
		try:
			fd = os.open('/dev/tty', os.O_RDWR | os.O_NOCTTY)
			os.close(fd)
		except OSError, err:
			if err.errno != errno.ENXIO:
				raise
				
		## Making current tty the head of the session
		os.setsid()
				
		## Checking if we've succeeded to disconnect from CTTY
		try:
			fd = os.open('/dev/tty', os.O_RDWR | os.O_NOCTTY)
			os.close(fd)
			## <<!>> It should not reach this point unless something goes wrong.
		except OSError, err:
			if err.errno != errno.ENXIO:
				raise
				
		
		## Checking if we have access to CHILD end of PTY pipe
		fd = os.open(child_name, os.O_RDWR)
		os.close(fd)
		
		## Regaining controlling rights of current terminal [skipping the O_NOCTTY]
		fd = os.open('/dev/tty', os.O_WRONLY)
		os.close(fd)



	def DAEMONIZE(self):
		"""
		Make this BUS run in a DAEMON mode. 
		Will trust single-fork method for now and see how it goes.
		maybe simply detaching from terminal would be enough... os.open("/dev/tty", os.O_NOCTTY), or smth like that
		"""
		try:
			pid = os.fork()
			if pid > 0: os._exit(0)
			
			#os.close(0)
			#os.close(1)
			#os.close(2)
			#os.setsid()
			
			_setControllingTTY(0)
			
			if self.F_LOGGEDIN:
				self._startReader()
		except Exception, e:
			print e

		

	def getTTYsize(self, fd):
		try:
			cr = struct.unpack('hh', fcntl.ioctl(fd, termios.TIOCGWINSZ,'1234'))
		except:
			return None, None
		return cr[1], cr[0]  ## (x, y)

	def setTTYsize(self, fd, col, row, xpix=0, ypix=0):
		winsize = struct.pack("HHHH", row, col, xpix, ypix)
		fcntl.ioctl(fd, termios.TIOCSWINSZ, winsize)

	def adaptTTYsize(self, signum=0, stack=None):
		
		localW, localH = self.getTTYsize(0)
		if localW == None or localH == None: return 2
		try:
			self.setTTYsize(self.parent_fd, localW, localH)
			return 0
		except:
			return 1


	def close(self):
		if self.F_CLOSING:
			self._debug("Already closing...")
			#return -1
		self.F_CLOSING			= True
		termios.tcsetattr(0, termios.TCSANOW, self.tc_orig_settings)
		""" Clean-up method """
		self._debug("Cleaning-up")
		self._debug("Called by: %s()" % _getFunctionName(2))
		self.F_LOGGEDIN 		= False
		self.F_HANDLEALTPIPES 	= False
		#self.F_RMTCLIENT 		= False
		self.F_CLIENTMODE       = False
		self.F_LOGGED           = False
		
		if self.attach_HANDLER:
			nodes=[]
			for node in self.attach_nodes:
				nodes.append(node)
				
			for node in nodes:
				try: 	self.removeAltNode(node)
				except:	pass
				
			self.attach_HANDLER.LEAVE()
		
		self._unblockPipes(RMT_NAMEPIPE + NAMEPIPE + STDINS_pending + STDINS, to_send=' ')
	
		if self.pid: # hasn't it been killed yet?
			try: ## killing child
				self._debug("Attempting to close parent_fd")
				os.kill(self.pid, self.SIG_CLOSE)
				self.pid = None
				self._debug("child PID should be killed now")
				#os.close(self.parent_fd)
			except Exception, ex:
				self._debug("Could not kill child process")
			

		try:
			self._debug("Trying to close all STDINS:" )
			self._debug(STDINS + STDINS_pending)
			self.Write(STDINS + STDINS_pending, '\x00') # unlocking FDs

			self._debug(self.socket_lsn)
		except Exception, ex:
			self._debug("Could not close socket: '%s'" % ex, "WARN")
#				pass

		if self.F_RMTCLIENT:
			try:
				self.F_RMTCLIENT = False
				self._debug("Attempting to close listening socket")
				s = socket.socket()
				s.connect((self.HOST, self.socket_port))
				s.close()
				## will close automatically
			except Exception, ex:
				self._debug("Error while unblocking and closing listening socket")
			
			self.F_RMTCLIENT = False
		"""
		if self.sockets_list:
			for sock, touple in self.sockets_list:
				print "closing socket"
				touple[2] = False
				sock.close()
		#"""
		try:
			self._debug("deleting child_fd")
			del self.child_fd ## os.close()'ing fd tends to be very noisy when descturtor kicks in
		except Exception,e:
			self._debug("Apparently I've failed to delete child PID on close()... See here: %s" % e, "ERR")
			pass
		
		try:
			self._debug("deleting parent_fd")
			del self.parent_fd ## os.close()'ing fd tends to be very noisy when descturtor kicks in
			#os.write(NAMEPIPE[0], '\n')
		except Exception,e:
			self._debug("Apparently I've failed to delete child PID on close()... See here: %s" % e, "ERR")
			pass
			
		self._debug("Restoring STDIN visibility")
		#self._enableCannonical(NAMEPIPE[0], True)
		#self._enableEcho(NAMEPIPE[0], True)
		##
		termios.tcsetattr(0, termios.TCSANOW, self.tc_orig_settings)
		
	
	
	
	
	
	## TERMIO related methods ##
	def _enableCannonical(self, fd, to_enable=True):
		""" 
		Method enables/disables cannonical mode for FD. 
		"""
		attr = termios.tcgetattr(fd)
		attr[3] = attr[3] & ~termios.ICANON

		if to_enable:
			attr[3] = attr[3] | termios.ICANON
			attr[6][termios.VMIN] = 1
		termios.tcsetattr(fd, termios.TCSANOW, attr)

	def _enableEcho(self, fd, to_enable=True):
		"""
		By default we're working in non-cannonical mode hence high latencies is not our friend..
		This function also sets terminal's ECHO mode for desired file descriptor
		"""
		
		attr = termios.tcgetattr(fd)
		attr[3] = attr[3] & ~termios.ECHO
		#attr[3] = attr[3] & ~termios.ICANON
		#attr[6][termios.VTIME] = 3
		#attr[6][termios.VMIN] = 1
		if to_enable:
			attr[3] = attr[3] | termios.ECHO
		termios.tcsetattr(fd, termios.TCSANOW, attr)
	
	def _muteSTDINs(self, mute=True):
		for stdin in STDINS:
			try:
				self._enableEcho(stdin, not mute)
			except Exception, ex:
				self._debug("Cannot mute/unmute terminal echo for %s: '%s'" % (stdin, ex))

	def _enable_C_Z(self, enabled=True, fd=STDIN_FILENO):
		self._debug("Setting 'C-Z ENABLED' to '%s'" % enabled)
		attr=termios.tcgetattr(fd)
		if enabled:
			attr[6][termios.VSUSP] = '\032'
		else:
			attr[6][termios.VSUSP] = '\000' #\032 sets it back to ^Z
		
		termios.tcsetattr(fd, termios.TCSANOW, attr)	
	
	
	## Automatic login related method ##
	def autoLogin(self, quiet=True, mode=1):
		""" Method automatically enters login information """
		
		''' MODES
			0 - STRICT-MANUAL. 	User will have to enter password manually
			1 - SEMI-AUTO. 		If none of given passwords fit -- user will be dropped to MANUAL mode
			2 - STRICT-AUTO. 	If none of given passwords fit -- method will return FALSE. Manual password entering will not be allowed
		'''
		
		""" Logic:
		  1. Read lines until we find "assword" substring is found in output. If we don't - timeout
		  2. Enter passphrase and keep reading lines.
		  3. If another "assword" is received:
		      a) use alternate password
		      b) enter interactive mode to enter password manually (possibly wait for interaction w/ timeout)
		      c) exit as failed to login on a first try...
		  4. If got 'assword' again - repeat (3) again. If password does not fit - terminate
		  5. If 'assword' was not received again - send "Hello" line to terminal and wait for response (w\ timeout enabled).
		#"""
		
		
		
		## Disabling that annoying and messy echoing.
		## Disable canonical  communication to allow keypresses pass through
		#self._debug("Disabling terminal echos and canonical mode (~termios.ICANON)")
		#self._enableEcho(RMT_NAMEPIPE[0], False)
		#self._enableCannonical(RMT_NAMEPIPE[0], False)
		
		self._enableEcho(RMT_NAMEPIPE[0], True)
		self._enableCannonical(RMT_NAMEPIPE[0], True)
		
		
		
		if 	 mode == 0:
			self.psws = []
			attempts=10
		elif mode == 1:
			attempts = 10
		elif mode == 2:
			attempts = len(self.psws)
		else:
			self._debug("Unknown login mode '%d'" % mode, "ERR")
			self.F_LOGGEDIN = False
			return False

		#elif mode == 2: attempts = 10
			
		self._debug("Running in mode %d with %d passwords" % (mode, attempts))
			
		
		attempt  = 0
		passwordSent = False
		testLineSent = False
		login_failed = False
		prompt = self.testLine
		self.mute    = True
		self.F_QUIET = quiet
		self.F_PAUSEREADER = True
		
		self._debug("Starting main autoLogin loop. F_LOGGEDIN=='%s'" % self.F_LOGGEDIN)
		while not (self.F_LOGGEDIN or login_failed):
			''' Okay. Here's how it works.
			First it retrieves a text block of self.readBufferSize size from remote connection.
			Then, if QUIET flag was set, it uses only the very last line of this output for further tests.
			
			It checks if host was not added to Trusted hosts file. If it hasn't - it adds it by typing 'yes\n' to terminal
			THEN it skips to another iteration...
			
			It checks if there's 'ssword' mentioned anywhere in the output. If so:
				1. If we are not asked to enter a new password we enter a provided one during construction [from global variables]. 
					Set local flag passwordSent to make futher checks aware that we were actually asked for a password and we've entered it.
					Skip to another iteration afterwards.
				2. If we are asked to enter a !new! password we mute STDIN echo and let user to enter it manually and skip to another iteration
					This is most likely to appear when account has expired and needs to change its password.
					Skip to another iteration afterwards.
				3. If password was already attempted to be sent and none of the above matched -- try to send ENTER. 
					Keep doing that until we keep getting the same reply. We'll assume this is the command prompt
					and treat it as LOGGED IN.
			#'''

			try:
				self._debug("__Reading line from child process__")
				rcvd_line = self.getLine([RMT_NAMEPIPE[1]], self.TIMEOUT_login, self.readBufferSize) ## getting child's stdout
				## We'll need to check if we received self.testLine anywhere in the output hence saving original output to separate variable.
				if self.F_QUIET:	## and using only last  line for what we need.
					self._debug("Quiet mode -- reducing output to the last line only")
					line = rcvd_line.replace('\r', '').split('\n')[-1]
				else:
					self._debug("non-quiet mode")
					line = rcvd_line
				if line == '': continue
			except TimeoutException, ex:
				## Well... Server did not respond for quite a while, 
				## so we're assuming it's not responding or hidden somewhere
				print "Timeout... (%d)" % self.TIMEOUT_login
				self.F_LOGGEDIN = False
				login_failed  = True
				continue
			except (InterruptedException, KeyboardInterrupt), ex:
				## Did you change your mind and press ^C?
				self._debug("Interrupted. Starting destruction", "CRIT")
				self.F_LOGGEDIN = False
				login_failed  = True
				continue
			except (select.error, os.error, Exception), err:
				## I have no idea what has just happened... Better just leave
				## and do not touch a thing....
				self._debug("FD error [%s] while reading line... Assuming we're logged out." % err, "CRIT")
				self.F_LOGGEDIN = False
				login_failed  = True
				continue
			
			if "continue connecting (yes/no)?" in line:
				self._debug("Ahh.. this host is not trusted yet. Adding it to the list (sending 'yes\\n')")
				try:
					os.write(RMT_NAMEPIPE[0], "yes\n")
				except Exception, e:
					self._debug("Cannot write to child. Error: '%s'" % e, "CRIT")
					self.login_failed = True
				continue
				
			if not self.mute or "password" in line.lower() or "disconnected mode login" in line.lower():
				## Let's see if we should print this out to the screen before proceeding
				self._debug("Writing line to stdout (possibly with password prompt)")
				self.Write(STDOUTS, line)
			else:
				self._debug("MUTTED :: '%s'" % line)
				
			if ("password" in line.lower() or "disconnected mode login" in line.lower()) and ":" in line:
				
				if attempt: self._debug("Attempt %d/%d" % (attempt+1, attempts), "WARN")
				
				if attempt == attempts:
					self._debug("We're out of attempts.")
					login_failed = True
					self.F_LOGGEDIN = False
					continue
				self._debug("All looks okay. Now we only have to enter a correct pw.")
					
				
				if "new" not in line:
					
					if len(self.psws) > attempt:					## if we're not out of predefined passwords (mode[1]; mode[2] should have terminated with the first IF in the loop)
						
						try:
							self.Write(STDOUTS, "********\n")
							self.pswd = self.psws[attempt]
							self.sendLine(self.pswd + '\n', return_ans=False) ## We want the following line to be caught by the loop
							passwordSent = True
							if not "(current)" in line: 
								attempt += 1
							continue
						except Exception, ex:
							## Not a clue what's wrong so I say we just leave
							self._debug("Error while sending password... something weird: '%s'. Leaving" % ex, "CRIT")
							self.F_LOGGEDIN = False
							login_failed  = True
							continue
						
					else:		## If we have no more predefined passwords (modes [0, 1])
						self._debug("No passwords were provided to enter automatically? Or are we out of guesses? Anyway -- enter pw manually", "WARN")
						try:
							self._muteSTDINs(True)
									
							self.pswd = self.getLine(STDINS, self.TIMEOUT_login, self.readBufferSize)
							self.Write(STDOUTS, "********\n")
							self.sendLine(self.pswd , return_ans=False)
							passwordSent = True
							if not "(current)" in line: 
								attempt += 1
							self._muteSTDINs(False)
							continue
						except Exception, ex:
							self._debug("Could not get a new password: '%s'. Leaving" % ex, "CRIT")
							self.F_LOGGEDIN = False
							login_failed  = True
							continue
						
						
								
				else: ## if we're asked to enter a new password
					
					self._debug("Looks like our old pw has expired. Enter new password manually", "WARN")
					try:
						
						self._muteSTDINs(True)
						
						self.pswd = self.getLine(STDINS, self.TIMEOUT_login, self.readBufferSize)
						
						print "********"
						self.sendLine(self.pswd)
						
						self._muteSTDINs(False)
						
						continue
					except Exception, ex:
						self._debug("Could not get a new password: '%s'. Leaving" % ex, "CRIT")
						self.F_LOGGEDIN = False
						login_failed  = True
						continue
			
			elif self.testLine in rcvd_line:
				self.F_LOGGEDIN = True
				self.sendLine("\n")
				#if not self.pswd: self.pswd = self.psws[attempt-1]
				self.attach_passphrase = self.pswd
				self._debug("Nice work! Looks like we're logged in as we managed to send '%s' to remote terminal and get it back!" % self.testLine)
				continue
			elif passwordSent:
				#if testLineSent: continue
				self.TIMEOUT_login = 2

				## If we have already entered a pw
				
				self._debug("Sending testLine to see if terminal is responding and sending it back")

				self.sendLine('echo \"%s\"\n' % self.testLine)
				
				testLineSent = True
				time.sleep(.1) ## A tiny delay to make sending-executing-reading not so atomic.
				''' ## alternate version
				#prompt = self.sendLine("\n", return_ans=True) 
				#print "prompted: '%s'" % prompt2
				if prompt == line:
					self._debug("'%s' == '%s'" % (prompt, line))
					self._debug("PROMPT MATCH")
					self.prompts['orig'] = prompt.replace('\r','').split('\n')[-1]
					print "Prompts: '%s'" % self.prompts
					self.F_LOGGEDIN = True
					self.mute = False
					continue
				self._debug("Resetting PROMPT to '%s'" % line)
				prompt = line
				self.sendLine('\n')
				#'''
				self._debug("Mutting futher lines from normal flow")
				#if quiet: self.mute = True
				self.mute = quiet
			
			
			else:
				#self._debug("MUTTED :: '%s'" % line)
				pass

		if login_failed:
			self._debug("Login failed. Closing connection", "ERR")
			self.close()
			return False
		#self.F_PAUSEREADER = False
		self._startReader()
		return True




	def prepareShell(self):
		if self.change_PS1 and 'shell' in self.OS:
			try:
				self._debug("Pausing READER")
				self.F_PAUSEREADER = True
				#self.sendLine(' ') ## unblocking READER
				self._unblockPipes([RMT_NAMEPIPE[1]], to_send=' ')
				self.sendLine('export PS1="%s" \n' % self.prompts[self.OS['shell']])
			except Exception, ex:
				self._debug("There's no predefined shell prompt for '%s'" % self.OS['shell'], "WARN")

		#self.sendLine('stty echo icanon ocrnl min 1' + '\n')

		self.F_PAUSEREADER = False
		self._debug("Un-pausing READER")

	## OS information related methods ##
	def _getOS(self, full=True):

		#self.isReady()
		
		self._debug("Pausing READER")
		self.F_PAUSEREADER = True
		#self.sendLine(' ') ## unblocking READER
		self._unblockPipes([RMT_NAMEPIPE[1]], to_send=' ')
		print "Gathering basic information..."
		#self.sendLine("sh\n", True)
		
		#self.sendLine("echo\n", True)
		self.sendLine("echo\n", False)
		self.uname = self.sendLine("uname -a\n", True).replace('\r', '').split('\n')
		self.OS['prompt'] = self.uname[-1] ## There might be many lines in the output, but it's expected that the last one will be a prompt for new command
		self.uname = self.uname[-2] ## and the one before last - output we require
				
		self.uname = self.uname.split(' ')
		self.OS['name'] = self.uname[0]
		self.OS['hostname'] = self.uname[1]
		self.OS['release'] = self.uname[2]
		self.OS['date'] = self.sendLine("perl -e 'print time, \"\\n\"' || /bin/date +\%s || echo UNKNOWN\n", True).replace('\r', '').split('\n')[-2]
		self.OS['uptime'] = self.sendLine("uptime\n", True).replace('\r', '').split('\n')[-2]
		self.OS['shell'] = self.sendLine("echo $0\n", True).replace('\r', '').split('\n')[-2].replace(' ', '').replace('-', '')
		self._debug("What info we've gathered about the OS: \n%s" % self.OS)
		self.F_PAUSEREADER = False
		self._debug("Un-pausing READER")
		#self.prepareShell();
		

	def _printOS(self):
		if not self.OS:
			os.write(NAMEPIPE[1], "You need to gather server information first.\n")
			return 1
		BUFFER  = "OS type:         " + self.OS['name']    + "\n"
		BUFFER += "OS release:      " + self.OS['release'] + "\n"
		BUFFER += "OS network name: " + self.OS['hostname']+ "\n"
		BUFFER += "OS uptime:       " + self.OS['uptime']  + "\n"
		BUFFER += "-----------------"                      + "\n"
		BUFFER += "SHELL:           " + self.OS['shell']   + "\n"
		BUFFER += "TimeStamp:       " + self.OS['date']    + "\n"
		os.write(NAMEPIPE[1], BUFFER + '\n')





	## READER thread starter ##
	def _startReader(self):
		if self.F_LOGGEDIN:
			self._debug("Looks like we're logged-in.. Trying to start a READER thread")
			try:
				self.reader = Thread(target=self.loopReaderThread, name="READER_thread")
				self.reader.start()
				self.adaptTTYsize()
				print ""

			except Exception, e:
				self.F_LOGGEDIN = False
				self._debug("Nope... I could not start the READER. Here's what I got: %s" % e, "ERR")
				return -1


	
	## READER thread body ##
	def loopReaderThread(self):
		""" A separate thread will perform the reading from remote server unless self.F_PAUSEREADER is enabled """

		self._debug("READER :: Starting READER thread")
		sleep_duration=0
		
		self._debug("READER :: Opening system file descriptor for PY file handler parent_fd")


		while self.F_LOGGEDIN:
			if self.F_PAUSEREADER: ## If we're about to expect output to pop up somewhere else in the script
				self._debug("READER :: thread is paused -- skipping and waiting for a second for status change")
				sleep_duration += 1
				if not sleep_duration % 10:
					self._debug("sleep_duration is now %d" % sleep_duration, "WARN")
					print "Script has been paused for %d seconds now -- probably just stuck. Restart it." % sleep_duration
					self.F_PAUSEREADER = False
				time.sleep(1)
				continue

			sleep_duration=0
			
			line = ''
			
			try:
				self._debug("Reading output from remote host")
				line = self.getLine([RMT_NAMEPIPE[1]], self.TIMEOUT_select_read, self.readBufferSize)
			except TimeoutException, e:
				continue
			except InterruptedException, e:
				#line = self.key.C_C
				#pass
				continue
			except (os.error, select.error), err:
				self._debug("Whoops... Something went wrong: %s\nSetting F_LOGGEDIN to FALSE and calling close()" % err, "ERR")
				self.F_LOGGEDIN = False
				self.close()
				continue
				
			try:
				self.Write(STDOUTS, line)
			except os.error, err:
				self._debug("Cannot write to STDOUT: '%s'" % err, "WARN")
			
			#os.kill(os.getpid(), signal.SIGINT)
		self._debug("---LEAVING READER THREAD---", "WARN")
	
	
	
	
	
	## Methods for checking shell availability ##
	def isReady(self, set_value=False):
		""" 
		Method sends testLine to remote end and if it replies with the same string it's assumed
		 that connection is established and it's fine to proceed with whatever
		"""
		if set_value:
			self._debug("Manually setting terminal READY state to: %s" % set_value)
			self.READY = set_value
			return self.READY
		
		if not self.READY:
			self._debug("READY flag has not been set yet. Running ECHO TESTLINE test")
			self._debug("Pausing READER thread")
			self.F_PAUSEREADER = True ## Pause READER thread
			self._debug("Unblocking READER thread with newline char if it was reading")

			#os.write(RMT_NAMEPIPE[0], "\n") ## unblocking READER
			self._unblockPipes([RMT_NAMEPIPE[1]], to_send=' ')
			self._debug("Sending 'echo %s\\n' to remote shell" % self.testLine)
			line = self.sendLine("echo %s\n" % self.testLine, return_ans=True)
			self._debug("Now searching this string for our testline: %s" % self.testLine[2:])
			if self.testLine[2:] in line:
				self._debug("FOUND IT! Setting READY flag to True")
				#self.isReady(True)
				self.READY = True
			#time.sleep(1) ## timeout to get response
			
			self._debug("UN-pausing READER thread")
			self.F_PAUSEREADER = False ## Un-pause READER thread
			
		self._debug("READY flag: %s" % self.READY)
		return self.READY
	
	def isInShell(self):
		"""
		Method checks if remote server is listening on a shell. 
		It simply sends newline twice and compares what it has received.
		"""
		self._debug("Checing if we're in shell prompt. Pausing READER thread")
		self.F_PAUSEREADER = True ## Pause READER thread
		
		attempt1 = self.sendLine('\n')
		time.sleep(.1)
		attempt2 = self.sendLine('\n')
		self._debug("Two samples were taken:\n1: '%s' \n2: '%s'\nUnpausing READER" % (attempt1, attempt2))
		self.F_PAUSEREADER = False ## Unpause READER thread
		
		return attempt1 == attempt2
	
	
	## INCOMPLETE ##
	def getLine(self, fd=[], timeout=None, buffer_size=1):
		
		if not timeout: timeout = self.TIMEOUT_command
		caller = _getFunctionName(2)
		try:
			self._debug("[@%s()] SELECTing" % caller)
			rFD = select.select(fd, [], [], timeout)[0]
			#if caller == "loopReaderThread" and self.F_PAUSEREADER: return ""
			self._debug("[@%s()] Selected... FD for reading: '%s'" % (caller, rFD))
			#print fd + rFD
			if rFD:
				self._debug("[@%s()] Reading from: '%s'" % (caller, rFD[0]))
				line = os.read(rFD[0], buffer_size)  ## returns String on success
				self._debug("[@%s()] Read line: '%s'" % (caller, line))
					
				return line
			else: 
				self._debug("[@%s()] Timed out while reading from '%s' for '%s' seconds" % (caller, fd, timeout))
				raise TimeoutException("[@%s()] Timed out while reading from '%s' for '%s' seconds" % (caller, fd, timeout), -1)
				
		
		except (KeyboardInterrupt), err:
			self._debug("[@%s()] Select(%s) has been interrupted by SIGINT" % (caller, fd))
			raise InterruptedException("[@%s()] SIGINT received while reading from fd: %s" % (caller, fd), -3)
		
		except select.error, err:
			self._debug("[@%s()] Unknown SELECT error: '%s'" % (caller, err), "ERR")

			raise select.error(err)
		
		except os.error, err:
			self._debug("[@%s()] Unknown READ error: '%s'" % (caller, err), "ERR")
			raise os.error(err)
			
		
	def Write(self, fds=[], line=""):
		caller = _getFunctionName(2)
		sent = 0
		
		for f in fds:
			try:
				sent += os.write(f, line)
			except (os.error, Exception), ex:
				self._debug("[@%s()] Could not write to %s", (caller, ex))
		return sent

	def removeSpaces(self, line=''):
		return line.replace('\n','').replace('\t','').replace(' ','')

	## Interaction with remote shell related functions ##
	def sendLine(self, line, return_ans=False, buffSize=None):
		""" 
		A os.write() wrapper that sends a line to remote host [no \n is added -- need to take care of this yourself].
		return_ans - will cause this method to take over reading from remote end of TTY.
		If method manages to detect a testLine (see in __init__) in output -- it asumes there was a test
		 and sets object variables so that it would look that connection to the host has been established 
		 successfully and it's responding well.
		"""
		if not buffSize: buffSize = self.readBufferSize
		sent=""
		try:
			self._debug("Attempting to write line to remote host")
			#sent = os.write(self.parent_fd, line)
			sent = os.write(RMT_NAMEPIPE[0], line)
		except Exception, e:
			self._debug("Whoops.. something went wrong: %s" % e, "ERR")
			pass
			
		if return_ans:
			self._debug("Will try to capture response from remote host")
			time.sleep(.5)
			self._debug("Capturing....")
			
			sent = self.getLine([RMT_NAMEPIPE[1]], self.TIMEOUT_command, buffSize)
			self._debug("Here's what we've received: %s" % sent)
		return sent
	
	def interact(self):
		""" Method allows user to interact with remote end manually [run commands, get response, etc...] """
		self._debug("Entering INTERACTIVE mode")
		if not self.F_LOGGEDIN:
			self._debug("Not logged in. Cannot start interactive mode", "CRIT")
			return -1
		

		try:
			self._enableEcho(RMT_NAMEPIPE[0] , False)
			self._enableCannonical(RMT_NAMEPIPE[0] , False)
			self._enable_C_Z(enabled=False)
			#self._getOS()
		except Exception, ex:
			self._debug("Problems while disabling ECHO for remote namepipe '%s': '%s'" % (RMT_NAMEPIPE[0], ex))
	
		for stdin in STDINS:
			try:
				self._enableCannonical(stdin, self.stdin_echo_enabled)
				self._enableEcho      (stdin,  False)
			except Exception, ex:
				self._debug("While trying to mute echo on one of stdin fd: '%s': '%s'" % (stdin, ex))


		buf=""
		

		while self.F_LOGGEDIN:

			line = ''
			
			try:
				self._debug("Reading command to send to remote host")
				line = self.getLine(STDINS, 3, 1)
				
			except TimeoutException, e:
				continue
			except InterruptedException, e:
				line = self.key.C_C
			except select.error, e:
				self._debug("select.error: '%s'" %e )
				continue
			except (os.error, select.error), e:
				self._debug("Whoops... Something went wrong: %s" % e, "ERR")
				self.F_LOGGEDIN = False
				self._debug("Setting F_LOGGEDIN to FALSE and calling close()")
				self.close()
				continue
				
			
			if line == self.key.DEL and self.stdin_echo_enabled: 
				self._debug(">Backspace<")
				self.Write(STDOUTS, self.key.BS)
				pass
				
			elif line == self.key.C_T: ## ^T
				self._debug("Cought C-T --> launching commandInterpreter")
				self._enable_C_Z(enabled=True)
				self._commandInterpreter()
				self._enable_C_Z(enabled=False)
				self._debug("Left commandInterpreter. Continuing interact() loop")
				continue

			try:
				self._debug("Sending: '%s'" % line)
				os.write(RMT_NAMEPIPE[0], line )
			except (os.error, Exception), err:
				self._debug("WRITE error to parent_fd: '%s'" % err, "ERR")
				self.F_LOGGEDIN = False
				continue
		self._debug("---LEAVING INTERACT()---")
				
			
	def sendScript(self, sFile="", argv="", argc=0):
		""" Method reads a locally stored script and sends it to remote host line-by-line """

		if sFile == "":
			self._debug("Script file was not passed to the function")
			return -1
		try:
			self._debug("Opening the script file '%s' for -read" % sFile)
			sf = open(sFile, 'r')
		except Exception, e:
			self._debug("Cannot open file '%s': %s" % (sFile, e), "ERR")
			return -1
		
		"""
		#self._debug("Checking if remote shell is ready")
		#if self.isReady():
		#self._debug("Yep.. It is. Reading script file now")
		#self.sendLine('\x04\n') ## Ctrl+C
		#self.sendLine('^C\n') ## Ctrl+C
		#"""
		
		if argc > 0:
			self.sendLine('export argv="%s"; export argc="%d"\n' % (argv, argc) )
		
		for line in sf:
			
			if line == '\n' or line == ' ':
				continue
			line += '\n'
			self._debug("sSending: %s" % line)
			self.sendLine("%s" % line)
					
		self._debug("Closing script file")
		try:
			sf.close()
		except Exception, e:
			self._debug("Could not close the script: %s" % e)
			return -1
		return 0




	
	
	def printAtPosition(self, x=-1, y=0, line="", fd=STDOUT_FILENO):
		os.write(fd, "\x1b7\x1b[%d;%df%s" % (x, y, line))
		return
	def printSpace(self, length=1):
		space=''
		for i in range(1, length):
			space+=' '
		return space
	def printAtColumn(self, x=0, line="", fd=STDOUT_FILENO):
		os.write(fd, "\033[%dG%s" % (x, line))
		return

	
	## Internal Command Interpreter related methods and variables ##
	# I know it's not pretty... will work on that later.. maybe :) #
	
	def i_send_pw_user		(self, command=[]):
		os.write(RMT_NAMEPIPE[0], self.pswd)
	
	def i_send_pw_session	(self, command=[]):
		os.write(RMT_NAMEPIPE[0], self.attach_passphrase)
		
	def i_send_user			(self, command=[]):
		os.write(RMT_NAMEPIPE[0], self.user)
	
	def i_send_script		(self, command=[]):
		try:
			path=''
			os.write(STDOUT_FILENO, "\nEnter path to the script you want to run (without spaces/tabs!) > ")
			self._enableCannonical(NAMEPIPE[0], True)
			self._enableEcho(NAMEPIPE[0], True)
			path = self.getLine([NAMEPIPE[0]], 60, self.readBufferSize)
			path = self.removeSpaces(path)
			if path:
				self.sendScript(path)
		except Exception, ex:
			self._debug("Could not send script (%s) : '%s'" % (path, ex), "ERR")
		self._enableCannonical(NAMEPIPE[0], False)
		
		
	def i_set_tty_mode_native(self, command=[]):
		self.sendLine('stty -echo 1>/dev/null 2>&1 \n')
		self.stdin_echo_enabled = True
		self._enableEcho(NAMEPIPE[0], True)
		os.write(NAMEPIPE[1]    , "NATIVE mode\n")
		
	def i_set_tty_mode_stty	(self, command=[]):
		self.sendLine('stty echo\n')
		self.stdin_echo_enabled = False
		self._enableEcho(NAMEPIPE[0], False)
		os.write(NAMEPIPE[1]    , "STTY mode\n")
	
	def i_set_tty_size_auto	(self, command=[]):
		self.adaptTTYsize()
	
	def i_set_tty_size_manual(self, command=[]):
		try:
			_W=0
			_H=0
			_W, _H = self.getTTYsize(self.parent_fd)
			
			os.write(STDOUT_FILENO, "Current Parent tty size (x, y): %s\n" % str(self.getTTYsize(self.parent_fd)))
			os.write(STDOUT_FILENO, "Current Child  tty size (x, y): %s\n" % str((_W, _H)))
			self._enableCannonical(NAMEPIPE[0], True)
			self._enableEcho(NAMEPIPE[0], True)
			os.write(STDOUT_FILENO, "Enter WIDTH  [empty to keep unchanged] > ")
			_Wnew = str(self.getLine([NAMEPIPE[0]], 60, self.readBufferSize)).split('\n')[0]
			os.write(STDOUT_FILENO, "Enter HEIGHT [empty to keep unchanged] > ")
			_Hnew = str(self.getLine([NAMEPIPE[0]], 60, self.readBufferSize)).split('\n')[0]
			
			
			if not _Wnew: _Wnew = _W
			if not _Hnew: _Hnew = _H
			self._debug("Setting TTY size to: (%s, %s)" % (_Wnew, _Hnew))
			self.setTTYsize(self.parent_fd, int(_Wnew), int(_Hnew))
			
			self._enableCannonical(NAMEPIPE[0], False)
		except Exception, e:
			print e
			self._enableCannonical(NAMEPIPE[0], False)
			self._debug("Could not change TTY size to (%s, %s): E: '%s'" % (_Wnew,_Hnew,e), "ERR")
	
	def i_set_pw_user		(self, command=[]):
		self._enableCannonical(NAMEPIPE[0], True)
		self._enableEcho(NAMEPIPE[0], False)
		self.Write([NAMEPIPE[1]], "Changing user password: > ")
		pw = self.getLine([NAMEPIPE[0]], 60, self.readBufferSize)
		self._enableCannonical(NAMEPIPE[0], False)
		self._enableEcho(NAMEPIPE[0], True)
		if pw != '':
			self.pswd = pw.replace('\n', '')
	
	def i_set_pw_session	(self, command=[]):
		self._enableCannonical(NAMEPIPE[0], True)
		self._enableEcho(NAMEPIPE[0], False)
		self.Write([NAMEPIPE[1]], "Changing session password: > ")
		pw = self.getLine([NAMEPIPE[0]], 60, self.readBufferSize)
		self._enableCannonical(NAMEPIPE[0], False)
		self._enableEcho(NAMEPIPE[0], True)
		if pw != '':
			self.attach_passphrase = pw.replace('\n', '')
	
	def i_set_clients_add	(self, command=[]):
		try:
			name=""
			os.write(STDOUT_FILENO, "Currently ALLOWED list looks like this:\n%s\n" % self.allowed_client_users)
			os.write(STDOUT_FILENO, "\nEnter username to add > ")
			self._enableCannonical(NAMEPIPE[0], True)
			self._enableEcho(NAMEPIPE[0], True)
			name = self.getLine([NAMEPIPE[0]], 60, self.readBufferSize)
			name = self.removeSpaces(name)
			if name:
				self.allowed_client_users.append(name)
		except Exception, ex:
			self._debug("Could not add another user (%s) to ALLOWED list: '%s'" % (name, ex), "ERR")
		self._enableCannonical(NAMEPIPE[0], False)
			
	def i_set_clients_remove(self, command=[]):
		try:
			name=""
			os.write(STDOUT_FILENO, "Currently ALLOWED list looks like this:\n%s\n" % self.allowed_client_users)
			os.write(STDOUT_FILENO, "\nEnter username to remove > ")
			self._enableCannonical(NAMEPIPE[0], True)
			self._enableEcho(NAMEPIPE[0], True)
			name = self.getLine([NAMEPIPE[0]], 60, self.readBufferSize)
			name = self.removeSpaces(name)
			if name:
				self.allowed_client_users.remove(name)
		except Exception, ex:
			self._debug("Could not add another user (%s) to the ALLOWED list: '%s'" %(name, ex), "ERR")
		self._enableCannonical(NAMEPIPE[0], False)
		
	def i_set_node_add		(self, command=[]):
		if command[-1] == "add":
			os.write(STDOUT_FILENO, "Enter name for new node > ")
			
			self._enableEcho(STDIN_FILENO, True)
			self._enableCannonical(STDIN_FILENO, True)
			node_name = self.getLine([STDIN_FILENO], 60, self.readBufferSize)[:-1].strip()
			self._enableCannonical(STDIN_FILENO, False)
			self._enableEcho(STDIN_FILENO, False)
		else:
			node_name = command[-1]
		if node_name:
			self.addAltNode(nodeName = node_name)
		
	def i_set_node_remove	(self, command=[]):
		if command[-1] == "remove":
			os.write(STDOUT_FILENO, "Enter node name for removal > ")
				
			self._enableEcho(STDIN_FILENO, True)
			self._enableCannonical(STDIN_FILENO, to_enable = True)
			node_name = self.getLine([STDIN_FILENO], 60, self.readBufferSize)[:-1].strip()
			self._enableCannonical(STDIN_FILENO, to_enable = False)
			self._enableEcho(STDIN_FILENO, False)
		else:
			node_name = command[-1]
		
		if node_name:
			try:
				self.removeAltNode(node_name)
			except: pass
		
#				self.attach_nodes[nodeName] = [stdin, stdout, pend_inp, outp]

		#self.attach_HANDLER.LEAVE()
		pass

	def i_set_node_base		(self, command=[]):
		if command[-1] == "base":
			os.write(STDOUT_FILENO, "Enter path for nodes > ")
			
			self._enableEcho(STDIN_FILENO, True)
			self._enableCannonical(STDIN_FILENO, True)
			basedir_name = self.getLine([STDIN_FILENO], 60, self.readBufferSize)[:-1].strip()
			self._enableCannonical(STDIN_FILENO, False)
			self._enableEcho(STDIN_FILENO, False)
		else:
			basedir_name = command[-1]
		
		
		self.attach_nodes_BASE = command[-1]

	def i_get_info			(self, command=[]):
		self._getOS()
		
	def i_show_info			(self, command=[]):
		self._printOS()

	def i_show_clients		(self, command=[]):
		os.write(STDOUT_FILENO, "Currently ALLOWED list looks like this:\n%s\n" % self.allowed_client_users)
	
	def i_show_attached		(self, command=[]):
		os.write(STDOUT_FILENO, "ATTACHED clients list:\n(#fd, [name, host, -rw])\n%s\n" % self.attached_clients)
		
	
	def i_show_nodes		(self, command=[]):
		if len(self.attach_nodes) > 0:
			for node in self.attach_nodes:
				os.write(STDOUT_FILENO, node + "\n")
				os.write(STDOUT_FILENO, "\tSTDIN  - " + str(self.attach_nodes[node][0]) + "\n")
				os.write(STDOUT_FILENO, "\tSTDOUT - " + str(self.attach_nodes[node][1]) + "\n")
		else:
			os.write(STDOUT_FILENO, "\tNo nodes set yet\n")
		
	def i_attach	(self, command=[]):
		self.sendAttachData(self.attach_passphrase)
		
	def i_help		(self, command=[]):
		last = self.interpreterMap2
		try:
			for elem in command:
				if elem == 'help':
					continue
				last = last[elem]
			print last['_info']
		except:
			for elem in last:
				try:
					if elem[0] == '_':
						continue
				except: pass
				os.write(STDOUT_FILENO, elem)
				self.printAtColumn(x=20, line='-- '+last[elem]['_info']+'\n', fd=STDOUT_FILENO)
				
		return
		
					
	def i_exit		(self, command=[]):
		os.write(RMT_NAMEPIPE[0], '\x03') ## ^C
		os.write(RMT_NAMEPIPE[0], ' exit\n')
		self.F_LOGGEDIN == False
		self.close()
		return 1
				
	
	interpreterMap2 = { 
	
			'send'  :{	'_info': "Sends some predefined data to remote host",
			
						'pw'	: { '_info'   : "Sends either user or session password to connected host. This way is typo-safe and you do ot have to worry that someone is glancing over your shoulder",
									'user'    : { '_info':"Sends user password to remote shell. Make sure to run this command where it s safe to",
												  '_run' :i_send_pw_user	},
									'session' : { '_info':"Sends session password to remote shell. I have no idea why would you need that, but just in case..",
												  '_run' :i_send_pw_session	},
									},
									
						'user'	: { '_info'	: "Sends your username to remote shell",
									'_run' 	: i_send_user	},
						'script': { '_info'	: "Sends locally stored script line-by-line to remote shell",
									'_run' 	: i_send_script	},
					  },

			'show'  :{	'_info'		: "Shows some data about a remote host",
						
						'info' 		: {	'_info' : "Shows some basic server information",
									'_run'  : i_show_info		},
						'clients'	: {	'_info' : "Shows list of clients allowed to attach this session in -rw mode",
									'_run'  : i_show_clients	},
						'attached'	: { '_info' : "Shows list of clients that are or were attached in -rw mode",
									'_run'  : i_show_attached	},
						'nodes'		: { '_info' : "Show attach() node related information",
									'_run'	: i_show_nodes		},
					 },
					 
			'set'   :{	'_info': "Sets some values and variables",
						
						'tty'	: 	{ '_info' : "Sets terminal-related settings.",
										  
									  'size'  : { 	'_info' : "Set Child tty size.",
														
													'auto'  : {	'_info': "Adjust TTY dimentions according to parent TTY",
																'_run' : i_set_tty_size_auto		},
													'manual': {	'_info': "Adjust TTY dimentions manually",
																'_run' : i_set_tty_size_manual	},
												},
									  'mode'  : {	'_info' : "Set terminal mode: either 'native' or 'stty'",
										
													'native': {	'_info': "Running in this mode all keypresses will be controlled by PySSH. This mode might lack of support for some keyboard keys",
																'_run' : i_set_tty_mode_native	},
													'stty'  : {	'_info': "Running in this mode all keypresses will be sent directly to remote shell. It's up to remote shell then what will arrow keys, backspace, etc. do. This is default mode.",
																'_run' : i_set_tty_mode_stty		},
												},
									},
						
						'pw'		: 	{ '_info' : "Set 'user' or 'session' password",
										  
										  'user'    : {	'_info': "Sets password of currently logged-in user (your user). Might be useful if it has changed during the session (passwd or so)",
														'_run' : i_set_pw_user			},
										  'session' : {	'_info':"Sets session password. Session password will be required for other users if they will attempt to attach in -rw mode.",
														'_run' : i_set_pw_session		},
										},
						'clients'	:	{ '_info'	: "Will add or remove attachable clients to/from ALLOWED list. These clients will have a chance to attach in -rw mode",
										  
										  'add'		: { '_info':"Will add another client to ALLOWED list",
														'_run' : i_set_clients_add		},
										  'remove'	: { '_info':"Will remove attachable client from the ALLOWED list",
														'_run' : i_set_clients_remove	},
										},
						'node'		: 	{ '_info'	: "Create/remove attach() nodes",
										  
										  'add'		: { '_info': "Add one mode attach() node",
														'_run' : i_set_node_add				},
										  'remove'	: { '_info': "Remove an attach() node",
														'_run' : i_set_node_remove			},
										  'base'	: {	'_info': "Path to BASE directory for attach() nodes",
														'_run' : i_set_node_base			},
										},
						},
						
			'get'	:{	'_info': "Gets some information from remote host",
						'info' : {	'_info'	: "Gathers basic host information",
									'_run'	: i_get_info	},
					},
			
			'attach':{'_run':i_attach, '_info':"Attach to a remote terminal"},
			
			'help'  :{'_run':i_help, '_info':"Show help page"       },
			'exit'  :{'_run':i_exit, '_info':"Exit from remote host"},
			'x'     :{'_run':i_exit, '_info':"Exit from remote host"}
					} #END
	
	def _commandInterpreter(self):
		self._debug("Entering command interpreter.")

		prompt = '!> '
		local_delim = ':'
		buffer_bit='-'
		#internal_command=''
		#esc_chars="\x1b" 				# characters that will exit the Interpreter's main loop (reading command)
		esc_chars="\x14" 				# characters that will exit the Interpreter's main loop (reading command)
		break_chars = '\n' + esc_chars 	# characters that will exit from the internal interpreter's loop
		
		os.write(NAMEPIPE[1], '\n [CI mode] %s\n' % self.CI_header)
		
		while not buffer_bit in esc_chars and self.F_LOGGEDIN: ## while not ^T and while we're in the server
			self._debug("Entered main Interpreter's loop. Enabling STDIN ECHO on terminal")
			self._enableEcho(NAMEPIPE[0], True)
			buffer_bit='-'
			CI_buffer=""
			internal_command=''
			os.write(NAMEPIPE[1], '\n' + prompt) ## Showing interaction prompt
			
			while not buffer_bit in break_chars:
				try:
					buffer_bit = os.read(NAMEPIPE[0], 1) 
				except (Exception, KeyboardInterrupt), ex:
					internal_command = ''
					buffer_bit='\n'
				
				
				if buffer_bit == self.key.DEL:
					internal_command = internal_command[:-1]
					os.write(NAMEPIPE[0], self.key.BS)
					continue
				
				elif buffer_bit == self.key.ESC: ## VT100 ESC key received. Starting to fill-in separate buffer with following chars.
					if CI_buffer == "":		
						CI_buffer += buffer_bit
						continue
					else: CI_buffer == ""
				elif (buffer_bit == "\x4f") or (buffer_bit == "\x5b"): ## A-hah! now we know it's one of navigation keys!
					if CI_buffer == "\x1b": 	
						CI_buffer += buffer_bit
						continue
					else: CI_buffer == ""
					
				elif (CI_buffer == "\x1b\x4f") or (CI_buffer == "\x1b\x5b"):
					if   buffer_bit == "\x41": ## UP
						CI_buffer = ""
						#print "UP"
						os.write(NAMEPIPE[1], self.key.DEL_LINE + '\r' + prompt)
						if not self.CI_H_position < 0:
							
							internal_command = self.CI_HISTORY[self.CI_H_position]
							os.write(NAMEPIPE[0], internal_command)
							self.CI_H_position -= 1
							
						continue
					elif buffer_bit == "\x42": ## DN
						CI_buffer = ""
						#print "DN"
						os.write(NAMEPIPE[1], self.key.DEL_LINE + '\r' + prompt)
						if self.CI_H_position < self.CI_H_length:
							self.CI_H_position += 1
							internal_command = self.CI_HISTORY[self.CI_H_position]
							os.write(NAMEPIPE[0], internal_command)
						else:
							internal_command = ""
						continue
						""" ## Will have to make this work... It's really annoying to not to have side keys working :/
						elif buffer_bit == "\x43": ## RH
							#print "RH"
							os.write(NAMEPIPE[0], self.key.DEL_4_L + self.key.GO_RIGHT)
							continue
						elif buffer_bit == "\x44": ## LH
							#print "LH"
							os.write(NAMEPIPE[0], self.key.DEL_4_L + self.key.GO_LEFT)
							continue
						"""
					else: CI_buffer = ""
				else:
				
					internal_command += buffer_bit
				
			self._debug("Command is: '%s'" % internal_command)
			
			if internal_command == '\n':
				self.CI_H_position = self.CI_H_length
				continue
				
			if buffer_bit == '\n':
				self._debug("Disabling STDIN echo (we do not need to see what command will be run on the machine... We just need it's output)")
				self._enableEcho(NAMEPIPE[0], False)
				
				internal_command = internal_command.strip(' \n')
				
				if not internal_command[0] == local_delim:
					
					self.CI_HISTORY.append(internal_command)
					self.CI_H_length += 1
					self.CI_H_position = self.CI_H_length
					
					self._parseInternalCommand(internal_command)
				
				else: ## We will analyze internal_command because it precedes with local_delim 
					##(delimiter indicating that we're not going to call callback function yet - something will need to be re-checked)
					internal_command = internal_command[1:] ## removing ':' at the begining and '\n' at the end

					if internal_command == "history":
						cnt = 0
						for h in self.CI_HISTORY:
							os.write(NAMEPIPE[1], "%d:\t%s\n" % (cnt, h))
							cnt += 1
					elif internal_command.isdigit() and int(internal_command) > 0 and not int(internal_command) > self.CI_H_length: ## We're running 
						self._parseInternalCommand(self.CI_HISTORY[int(internal_command)])
					
		#print self.CI_HISTORY
		self._enableEcho(NAMEPIPE[0], self.stdin_echo_enabled)
		self._debug("Leaving interpreter as char '%s' is one of ESC chars: '%s'" % (buffer_bit, esc_chars))
		return

	def _parseInternalCommand(self, line):
		""" 
		Private method is meant to parse string user enters by hand and see if
		it is meant to be sent to remote server or it should be interpreted
		by PySSH itself.
		
		#USING interpreterMap2
		this map is a tree of dictionaries. Each branch has element "_info":"Some info about the branch"
		Terminal branches suppose to have effective elements "_run":function_name_to_call. 
		This function will be passed two args: this ssh object and an array of CI commands 
		 """
		
		
		command = line.split()
		last=self.interpreterMap2
		
		try: ## Narrowing down to the terminal branch
			for elem in command:
				last = last[elem]
		except: ## Break if could not find some branch
			pass
			

		
		try:
			## Terminal branches should have "_run". If it does not have it -- show info and return to CI shell
			## If _run is found and it is not a terminal branch - remaining <elem>s will be passed as <command> arg.
			last['_run'](self, command)
			return 1
		except:
			try:
				self.interpreterMap2['help']['_run'](self, command)
			except Exception, ex:
				self._debug("Could not run 'help _run' for command: '%s'" % last, "ERR")
			os.write(STDOUT_FILENO, "unknown command '%s'.\nTry 'help' or 'help some_command' or 'help some_command *' command for more info \n" % command)
		return 0
		
		self.Write([ NAMEPIPE[1] ]    , "unknown command '%s'. use 'help' command for more info\n" % command)
		return -1



	
	
	def _interruptHandler(self, signal, frame):
		self.close() 



	def _unblockPipes(self, pipes=[], to_send=" "):
		if len(pipes) == 0:
			pipes = RMT_NAMEPIPE + NAMEPIPE
		self._debug("Unblocking pipes: '%s'" % str(pipes))
		for pipe in pipes:
			try:	os.write(pipe, to_send)
			except:	pass
	
	def __del__(self):
		self.close()
		print "\rBye bye [%s]!" % self.host




class Keys:
	def __init__(self):
		self.ESC = '\x1b'
		self.BS  = '\x08 \x08\x08 \x08\x08 \x08 \x08'
		self.C_C = '\x03'
		self.DEL = '\x7f'
		self.C_T = '\x14'
		self.C_Z = '\x1a'
		#self.C_Z = '\032'
		self.GO_LEFT  = self.ESC + '[D'
		self.GO_RIGHT = self.ESC + '[C'
		self.DEL_LINE = self.ESC + '[2K'
		self.DEL_1_L = self.GO_LEFT + 												' '
		self.DEL_2_L = self.GO_LEFT + self.GO_LEFT + 								'  ' 	+ self.GO_LEFT + self.GO_LEFT
		self.DEL_3_L = self.GO_LEFT + self.GO_LEFT + self.GO_LEFT + 				'   ' 	+ self.GO_LEFT + self.GO_LEFT + self.GO_LEFT
		self.DEL_4_L = self.GO_LEFT + self.GO_LEFT + self.GO_LEFT + self.GO_LEFT + 	'    ' 	+ self.GO_LEFT + self.GO_LEFT + self.GO_LEFT + self.GO_LEFT




def ping(self, host=None, reply_timeout = 2, packet_count = 1, path_to_ping = "/bin/ping"):
	""" Uses native ping tool to ping the host. Returns touple: (ReturnCode, STDOUT, STDERR) """
	if not host: return []
	
	null = open(os.devnull, 'wb')
	pinger = Popen([path_to_ping, "-q", "-W", str(reply_timeout), "-c", str(packet_count), host], stdout=PIPE, stderr=PIPE)
	out, err = pinger.communicate()
	null.close()
	self._debug("Ping to '%s' status:" % (host))
	self._debug("STDOUT: %s" % out)
	if err: self._debug("STDERR: %s" % err, "CRIT")
	return (pinger.returncode, out, err )



class TextFormat:
	txt_normal='\e[0m'
	txt_lred='\e[91m'
	txt_red='\e[31m'
	txt_lgreen='\e[92m'
	txt_green='\e[32m'
	
	txt_bold='\e[1m'
	txt_nobold='\e[21m'

class TimeoutException(Exception):
	def __init__(self, message, code):
#		super(TimeoutException, self).__init__(message)
		self.message = message
		self.code    = code

class InterruptedException(Exception):
	def __init__(self, message, code):
#		super(InterruptedException, self).__init__(message)
		self.message = message
		self.code    = code


