from socket import *
import time
import math
import json


def delay(i): # makes some irregular bumps, .8 keeps it positive
    return .3 * math.cos(10*i) + .3 * math.sin(5*i) + .8

def send_audio(connectionSocket):
    packets_sent = 0
    while True:
        time.sleep(1) #time for recording audio
        time.sleep(delay(packets_sent)) #net latency
        packet = json.dumps({'send time': time.time(),
                             'audio': packets_sent,
                             'talkspurt end': False})
        connectionSocket.send(packet.encode())
        packets_sent = packets_sent + 1

serverPort = 12000
serverSocket = socket(AF_INET,SOCK_STREAM)
serverSocket.bind(('',serverPort))
serverSocket.listen(1)
print('The server is ready to receive')
        

while True:
    connectionSocket, addr = serverSocket.accept()
    send_audio(connectionSocket)
    
    

