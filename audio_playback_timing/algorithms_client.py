from socket import *
import json
import time
import os
import sys

# Variables used in the algorithms:
# t_i, a_i, p_i = send, arrival, playout time
# d_i = p_i - t_i
# n_i = a_i - t_i
# b_i = p_i - a_i
# v_hat = variance estimate
# d_hat = d_i estimate
#
#
# Variables specifically used in algo 4
#
# normal mode (True/False) = False if there is currently
# a latency spike
#
# var = roughly tracks the slope of the spike so the
# algo knows when the spike is over


def parse(clientSocket):
    packet = clientSocket.recv(1024)
    packet = json.loads(packet.decode())
    t_i = packet['send time']
    a_i = time.time()
    n_i = a_i - t_i
    return packet, t_i, n_i


def add_to_playout_buffer(b_i, audio):
    n = os.fork()
    if n == 0:
        if b_i > 0:
            time.sleep(b_i)
        print(f"playing {audio} at {time.time()}")

def linear_interp_dhat(algo_state, alpha):
    algo_state['d hat'] = alpha * algo_state['d hat']\
        + (1 - alpha) * algo_state['n i']

def linear_interp_vhat(algo_state, alpha):    
    algo_state['v hat'] = \
        alpha * algo_state['v hat'] + \
        (1 - alpha) * abs(algo_state['d hat'] - \
                          algo_state['n i'])

def algo1(algo_state):
    alpha = .998 #used in paper
    linear_interp_dhat(algo_state, alpha)
    linear_interp_vhat(algo_state, alpha)
    

def algo2(algo_state):
    alpha = .998
    beta = .75
    
    if algo_state['n i'] > algo_state['d hat']:
        linear_interp_dhat(algo_state, beta)
    else:
        linear_interp_dhat(algo_state, alpha)
    linear_interp_vhat(alpha)

# algo 3 didn't seem that interesting to implement

def algo4(algo_state):
    if algo_state['normal mode']:
        if abs(algo_state['n i'] - algo_state['n (i - 1)']) > \
           abs(algo_state['v hat']) * 2 + 800:
            algo_state['var'] = 0
            algo_state['normal mode'] = False

    else:
        algo_state['var'] = \
            algo_state['var']/2 + \
            abs(2 * algo_state['n i'] - \
                algo_state['n (i - 1)'] - \
                algo_state['n (i - 2)'])/8
        if algo_state['var'] <= 63:
            algo_state['normal mode'] = True
            algo_state['n (i - 2)'] = algo_state['n (i - 1)']
            algo_state['n (i - 1)'] = algo_state['n i']
            return

    if algo_state['normal mode']:
        linear_interp_dhat(algo_state, .875)
    else:
        algo_state['d hat'] = \
            algo_state['d hat'] +\
            algo_state['n i'] -\
            algo_state['n (i - 1)']
    linear_interp_vhat(algo_state, .875)
    algo_state['n (i - 2)'] = algo_state['n (i - 1)']
    algo_state['n (i - 1)'] = algo_state['n i']
            

algo_state = {'d hat':0.,
              'v hat':0.,
              'n i':0.,
              #fields below are for algo 4
              'n (i - 1)':0.,
              'n (i - 2)':0.,
              'normal mode':True, #False indicates a latency spike
              'var':0., #roughly measures the slope of a spike
                        #to track when it ends
              }
    
serverName = ''
serverPort = 12000

clientSocket = socket(AF_INET, SOCK_STREAM)
clientSocket.connect((serverName,serverPort))

playout_buffer = {}
algo_update = algo1
while True:
    first_packet_in_spurt, t_first_in_spurt, n_first_in_spurt = \
        parse(clientSocket)
    algo_state['n i'] = n_first_in_spurt
    algo_update(algo_state)
    
    p_first_in_spurt = \
        time.time() + \
        algo_state['d hat'] + 4 * algo_state['v hat']
    add_to_playout_buffer(p_first_in_spurt - time.time(),
                          first_packet_in_spurt['audio'])

    while True:
        packet, t_i, n_i = parse(clientSocket)
        algo_update(algo_state)
        p_i = p_first_in_spurt - t_first_in_spurt + t_i
        add_to_playout_buffer(p_i - time.time(),
                              packet['audio'])
        if packet['talkspurt end']:
            break
    


