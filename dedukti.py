import sys
from parser import sigparser as parser

def dkcheck(sigs):
    for (mod,sig) in sigs:
        print(f"Module: {mod}")
        for i in sig:
            print(i)

if __name__ == "__main__":
    with open(sys.argv[1], 'r') as f:
        sigs = parser.parse(f.read())
        dkcheck(sigs)
