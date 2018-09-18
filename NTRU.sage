#!/usr/bin/env sage -python

from sage.all import *
import sys
import math

# global variables known to everyone
N = 20      # best to be kept <= 20 (with bigger values my laptop tries to fly into outer space)
p = 7       # must be prime and relatively small <= 7
q = 1048576 # must be a large power of 2
d = 11      # number of nonzero integer coefficients used in generated polynomials

# a class Zx of polynomials with integer coefficients and x as an unknown variable
Zx.<x> = ZZ[]

# ----------------------------------------------- AUXILIARY OPERATIONS ----------------------------------------------- 
def invertmodprime(f,p):
    ''' calculates an inversion of a polynomial modulo x^N-1 and then modulo p
        with assumption that p is prime.

        returns a Zx polynomial h such as convolution of h ~ f = 1 (mod p)                
        raises an exception if such Zx polynomial h doesn't exist'''

    T = Zx.change_ring(Integers(p)).quotient(x^N-1) # T is a quotient ring constructed from Zx after it's base being changed to Zp
    return Zx(lift(1 / T(f)))                       # with an use of an ideal x^N-1. Lift function converts Zp/x^N-1 back into Zp. 

def invertmodpowerof2(f,q):
    ''' calculates an inversion of a polynomial modulo x^N-1 and then modulo q
        with assumption that q is a power of 2.

        returns a Zx polynomial h such as convolution of h ~ f = 1 (mod q)                
        raises an exception if such Zx polynomial h doesn't exist'''

    assert q.is_power_of(2)     # asserting that q is a power of 2
    h = invertmodprime(f,2)     # first get an inversion of a polynomial like above with a prime number 2
    while True:
        r = balancedmod(convolution(h,f),q)         # get convolution of f and h (mod q) with balance
        if r == 1: return h                         # h * f = 1 (mod q), means h is a reciprocal of f       
        h = balancedmod(convolution(h,2 - r),q)     # get convolution of h and 2-r (mod q) with balance    

def balancedmod(f,q):
    ''' reduces every coefficient of a Zx polynomial f modulo q
        with additional balancing, so the result coefficients are integers in interval [-q/2, +q/2]
        more specifically: for an odd q [-(q-1)/2, +(q-1)/2], for an even q [-q/2, +q/2-1]. 

        returns Zx reduced polynomial'''

    g = list(((f[i] + q//2) % q) - q//2 for i in range(N))
    return Zx(g)

def convolution(f,g):
    ''' performs a multiplication operation specific for NTRU, which works like a traditional polynomial multiplication
        with additional reduction of the result by x^N-1 (x^n is replaced by 1, x^n-1 by x, x^n-2 by x^2, ...)

        returns Zx polynomial'''
    
    return (f * g) % (x^N-1)

# ----------------------------------------------- BASIC SETUP -----------------------------------------------
def validate_params():
    ''' checks params meet certain conditions: if q is considerably larger than p
        and if greatest common divider of p and q is 1 
        
        returns N, p, q '''
  
    if q > p and gcd(p,q) == 1:
        return True
    return False

def generate_polynomial(d):
    ''' generates a random polynomial with d nonzero coefficients

        returns Zx polynomial '''

    assert d <= N       # asserting that there are less nonzero coefficients given than number of all coefficients
    result = N*[0]      # vector variable to keep the result
    for j in range(d):  
        while True:
            r = randrange(N)            # get a random index < N    
            if not result[r]: break     # if there is no coefficient in this place of a vector 
        result[r] = 1-2*randrange(2)    # add a random number from a set {-1,0,1} in this place 
    return Zx(result)

# ----------------------------------------------- MAIN SETUP -----------------------------------------------
def generate_keys():
    ''' generates a public and private key pair, based on provided parameters

        returns Zx public key and a secret key as a tuple of Zx f (private key) and Zx F_p'''

    # validate params
    if validate_params():

        #   some polynomials are not invertible and as f and g are calculated randomly,
        #   it may be necessary to skip some invalid examples
        while True:
            try:
                # generate 2 random polynomials f and g with number of nonzero coefficients < given number
                f = generate_polynomial(d)
                g = generate_polynomial(d)

                # formula: find f_q, where: f_q (*) f = 1 (mod q)
                # assuming q is a power of 2                 
                f_q = invertmodpowerof2(f,q)

                # formula: find f_p, where: f_p (*) f = 1 (mod p) 
                # assuming p is a prime number 
                f_p = invertmodprime(f,p)  
                break
        
            except:
                pass 
    
        #formula: public key = F_q ~ g (mod q)
        public_key = balancedmod(p * convolution(f_q,g),q)

        #secret key is a tuple containing a private key (f) and variable f_p needed for decryption
        secret_key = f,f_p

        return public_key,secret_key

    else:
        print("Provided params are not correct. q and p should be co-prime, q should be a power of 2 considerably larger than p and p should be prime.")

#---------------------------------- ENCRYPTION -----------------------------------------
def generate_message():
    ''' creates a polynomial from a random list of coefficients selected from a set {-1,0,1}  

        returns Zx polynomial'''
        
    #randrange(3) - 1 gives results from a set of {-1,0,1}, which is necessary for a proper decryption
    result = list(randrange(3) - 1 for j in range(N))
    return Zx(result)

def encrypt(message, public_key):
    ''' performs encryption of a given message using a provided public key

        returns Zx encrypted message'''

    # generate random polynomial with number of nonzero coefficients < N for adding extra noise    
    r = generate_polynomial(d)

    # formula: encrypted_message = p * r ~ public_key + message (mod q)
    # while performing modulo operation, balance coefficients of encrypted_message 
    # for the integers in interval [-q/2, +q/2]
    return balancedmod(convolution(public_key,p*r) + message,q)


def decrypt(encrypted_message, secret_key):
    ''' performs decryption of a given ciphertext using an own private key
        
        returns Zx decrypted message'''
    
    # private key - f; additional variable stored for decryption - f_p     
    f,f_p = secret_key
    
    # formula: a = f ~ encrypted_message (mod q)
    # balance coefficients of a for the integers in interval [-q/2, +q/2]
    a = balancedmod(convolution(encrypted_message,f),q)
     
    # formula: F_p ~ a (mod p) with additional balancing as above
    return balancedmod(convolution(a,f_p),p)

#----------------------------------------------------------------------------------------
#-------------------------------------- MAIN --------------------------------------------
#----------------------------------------------------------------------------------------

public_key, secret_key = generate_keys()
message = generate_message()
print("MESSAGE: " + str(message))

encrypted_message = encrypt(message, public_key)
print("ENCRYPTION: " + str(encrypted_message))

decrypted_message = decrypt(encrypted_message, secret_key)
print("DECRYPTION: " + str(decrypted_message))

if message == decrypted_message:
    print("SUCCESS")
else:
    print("FAIL")

sys.exit()
