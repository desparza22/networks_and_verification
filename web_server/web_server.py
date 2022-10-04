#import socket module
from socket import *
import sys # In order to terminate the program

serverSocket = socket(AF_INET, SOCK_STREAM)
#Prepare a server socket
serverPort = 80
serverSocket.bind(('', serverPort))
serverSocket.listen(1)


while True:
 #Establish the connection
 print('Ready to serve...')
 connectionSocket, addr = connectionSocket, addr = serverSocket.accept()
 try:
     message = connectionSocket.recv(1024).decode()
     print(message)
     if(len(message.split()) < 2):
         continue
     filename = message.split()[1]

     if "favicon" in filename:
         f = open(filename[1:], "rb")
         outputdata = [
             "Content-Type: image/ico\r\n",
             "Keep-Alive: timeout=max=100\r\n",
             "Connection: Keep-Alive\r\n"]

         
         #Send one HTTP header line into socket
         connectionSocket.send("HTTP/1.1 200 OK\r\n".encode())
         #Send the content of the requested file to the client
         for i in range(0, len(outputdata)):
             connectionSocket.send(outputdata[i].encode())
         connectionSocket.send("\r\n".encode())
         connectionSocket.sendall(f.read())
         connectionSocket.send("\r\n".encode())

     else:
         f = open(filename[1:])
         outputdata = [
             "Content-Type: text/html\r\n",
             "Keep-Alive: timeout=max=100\r\n",
             "Connection: Keep-Alive\r\n",
             f"\r\n{f.read()}\r\n"]

         #Send one HTTP header line into socket
         connectionSocket.send("HTTP/1.1 200 OK\r\n".encode())
         #Send the content of the requested file to the client
         for i in range(0, len(outputdata)):
             connectionSocket.send(outputdata[i].encode())
     
     connectionSocket.close()
 except IOError:
     #Send response message for file not found
     connectionSocket.send("HTTP/1.1 404 NOT FOUND\r\n".encode())
     #Close client socket
     connectionSocket.close()
     
     #serverSocket.close()
     #sys.exit()#Terminate the program after sending the corresponding data 
