import random
import math
import numpy as np
import datetime
import time
import matplotlib.pyplot as plt
def clean(x):
  return list(dict.fromkeys(x))
class Node:
    pass
#Tree logic operator definitions
class And(Node):
    def __init__(self,inputs):

        self.numInputs = 2
        self.inputs = inputs

    def evaluate(self):
        return self.inputs[0].evaluate() and self.inputs[1].evaluate()
class Nand(Node):
    def __init__(self,inputs):

        self.numInputs = 2
        self.inputs = inputs

    def evaluate(self):
        if(len(self.inputs) < 2):
            return not self.inputs[0].evaluate()
        return not(self.inputs[0].evaluate() and self.inputs[1].evaluate())
    def __str__(self):
        return "Nand"
class Or(Node):
    def __init__(self,inputs):

        self.numInputs = 2
        self.inputs = inputs

    def evaluate(self):
        return self.inputs[0].evaluate() or self.inputs[1].evaluate()
class Not(Node):
    def __init__(self, inputs):
        self.inputs = inputs
        self.numInputs = 1

    def evaluate(self):
        return not self.inputs[0].evaluate()
class Const(Node):
    def __init__(self, value, name = "NONAME"):
        self.name = name
        self.inputs = []
        self.numInputs = 0
        self.value = value
    def evaluate(self):
        return self.value
    def setValue(self,value):
        self.value = value
    def __str__(self):
        return "Const: " + self.name
#Defining elements of solver datastructure looking back the remaining structure seems like it can be removed as the algortihm runs but for now I leave it as a skeleton
class Branch():
    def __init__(self):
        self.left = None
        self.right = None
    def __str__(self):
        return "Branch"
class Facts():
    def __init__(self):
        self.facts = []
        self.branch = None
    def __str__(self):
        ret = "Facts "
        for fact in self.facts:
            ret += " " + fact[0].__str__() + " "+ str(fact[1])
        return ret
    def __repr__(self):
        ret = "Facts "
        for fact in self.facts:
            ret += " " + fact[0].__str__() + " "+ str(fact[1])
        return ret
#Take a tree of NAND logic and generate a tree giving required states of inputs
def recursiveBuildSatisfactionTree(tree,branchct,opCount):
    opCount[0] +=1

    opCount[0] +=1
    if(type(tree) == Facts):
        opCount[0]+=1
        resolve = None
        #flag = True
        cont_flag = True
        seen = []
        for fact in tree.facts:
            opCount[0]+=1
            if(type(fact[0]) != Const):
                resolve = fact
                break
                #flag = False
        if resolve != None:
            if(resolve[1]):
                if(len(resolve[0].inputs) > 1):
                    opCount[0]+=1
                    br = Branch()
                    br.left = Facts()
                    br.left.facts.append((resolve[0].inputs[0],False))
                    br.right = Facts()
                    br.right.facts.append((resolve[0].inputs[1],False))
                    tree.facts.remove(resolve)
                    f1 = True
                    f2 = True
                    while len(tree.facts) > 0:

                         opCount[0]+=1
                         br.right.facts.append(tree.facts[0])
                         br.left.facts.append(tree.facts[0])

                         tree.facts.pop(0)
                         for fact in tree.facts:
                             opCount[0]+=1
                             if(fact[0] == br.left.facts[-1][0] and fact[1] != br.left.facts[-1][1]):
                                opCount[0]+=1
                                f1 = False
                             if(fact[0] == br.right.facts[-1][0] and fact[1] != br.left.facts[-1][1]):
                                opCount[0]+=1
                                f2 = False


                    if(f1 and f2):
                        opCount[0]+=1
                        branchct[0] +=1
                        tree.branch = br
                        recursiveBuildSatisfactionTree(tree.branch,branchct,opCount)
                        return
                    if(f1):
                        opCount[0]+=1
                        tree.facts = br.left.facts
                        tree.facts.append((resolve[0].inputs[0],False))
                        recursiveBuildSatisfactionTree(tree,branchct,opCount)
                        return
                    if(f2):
                        tree.facts = br.right.facts
                        opCount[0]+=1
                        tree.facts.append((resolve[0].inputs[1],False))
                        recursiveBuildSatisfactionTree(tree,branchct,opCount)
                        return
                else:
                    opCount[0]+=1
                    tree.facts.append((resolve[0].inputs[0], False))
                    tree.facts.remove(resolve)
                    recursiveBuildSatisfactionTree(tree,branchct,opCount)
            else:
                opCount[0]+=1
                tree.facts.append((resolve[0].inputs[0], True))
                if len(resolve[0].inputs) > 1:
                    opCount[0]+=1
                    tree.facts.append((resolve[0].inputs[1], True))
                tree.facts.remove(resolve)
                recursiveBuildSatisfactionTree(tree,branchct,opCount)
        else:
            opCount[0]+=1
            return
    if(type(tree) == Branch):
        if tree.left != None:
            opCount[0]+=1
            recursiveBuildSatisfactionTree(tree.left,branchct,opCount)
        if tree.right != None:
            opCount[0]+=1
            recursiveBuildSatisfactionTree(tree.right,branchct,opCount)
#Print special datastructure for debug
def printTree(tree,level = 0):
    if tree == None:
        return
    if(type(tree) == Branch):

        print("\t" * level, tree.left.__str__())
        printTree(tree.left,level + 1)
        print("\t" * level, tree.right.__str__())
        printTree(tree.right,level + 1)
    else:

        print("\t" * level, tree.branch.__str__())
        printTree(tree.branch,level + 1)
#Print NAND logic circuit
def printCircuit(circ, level=0):
    if(circ) == None:
        return
    if(type(circ) == Const):
        print("\t" * level,circ.__str__())
    else:
        if(len(circ.inputs) > 1):
            print("\t" * level,circ.__str__())
            printCircuit(circ.inputs[0],level + 1)
            #print("\t" * level, circ.inputs[1].__str__())
            printCircuit(circ.inputs[1],level + 1)
        else:
            print("\t" * level,circ.__str__())
            printCircuit(circ.inputs[0],level + 1)
#Get all leaves of a sat tree
def collectLeaves(root, leaves):
    if(type(root) == Branch):
        if(root.left != None):
            collectLeaves(root.left, leaves)
        if(root.right != None):
            collectLeaves(root.right, leaves)
        if(root.left == None and root.right == None):
            leaves.append(root)
    if(type(root) == Facts):
        if(root.branch != None):
            collectLeaves(root.branch, leaves)
        else:
            leaves.append(root)

#Get all inputs to a NAND circuit
def collectInputGates(root, gates):
    if(type(root) == Nand):
        if(len(root.inputs) > 1 and root.inputs[1] == None):
            if not root in gates:
                gates.append(root)
        if(root.inputs[0] == None):
            if not root in gates:
                gates.append(root)

        if(len(root.inputs) > 1 and root.inputs[1] != None and type(root.inputs[1]) != Const):
            collectInputGates(root.inputs[1], gates)
        if(root.inputs[0] != None and type(root.inputs[0]) != Const):
            collectInputGates(root.inputs[0], gates)



#Remove leaves that require contradictory states
def clearContradictingLeaves(leaves):
    for leaf in leaves:
        flag = False
        for i in range(0, len(leaf.facts)):
            if flag:
                break
            for j in range(i + 1, len(leaf.facts)):
                if(leaf.facts[i][0].name == leaf.facts[j][0].name and leaf.facts[j][1] != leaf.facts[i][1]):
                    leaves.remove(leaf)
                    flag = True
                    break
#Remove duplicates from lists
def removeDuplicateFacts(leaves):

    for leaf in leaves:
         newFacts = []
         for i in range(0, len(leaf.facts)):
            if not leaf.facts[i] in newFacts:
                newFacts.append(leaf.facts[i])
         leaf.facts = newFacts
#Sort a list
def orderFacts(leaves):
    for leaf in leaves:
        leaf.facts = sorted(leaf.facts, key = lambda x:x[0].name)
#Generate possible satisifier values by covering each free parameter and tacking on required params
def generateSatisfiers(leaves, inps):
    satisfiers =[]
    for leaf in leaves:
        free = len(inps) - len(leaf.facts)
        for i in range(0,int(2**free)):
            #print(i)
            unused = 0
            satis = ""
            t = bin(i)[2:]
            t = "0" * (free - len(t)) + t
            for inp in inps:
                flag = True
                temp = (inp[1],True)
                if temp in leaf.facts:
                    satis+="1"
                    continue
                temp = (inp[1],False)
                if temp in leaf.facts:
                    satis+="0"
                    continue
                satis+= (t)[unused]
                unused+=1
            satisfiers.append(satis)
    return clean(satisfiers)
#Build random NAND logic to test on
def improvedNandCircuitBuilder(n,inps):
    root = Nand([None,None])
    tempInps = []
    rootT = Nand([None,Nand([Nand([Nand([None,None]),Nand([Nand([None]),Nand([None])])]),Nand([None,None])])])
    collectInputGates(rootT, tempInps)
    numGates = 1
    while(numGates < n):
        tempInps = []
        collectInputGates(root, tempInps)
        placedGate = False
        for i in range(len(tempInps)):
            if(i == len(tempInps) - 1 and not placedGate):
                if(len(tempInps[i].inputs) < 2):
                    if(tempInps[i].inputs[0] == None):
                        if(random.randint(0,100) > 50):
                            if numGates < n:
                                numGates +=1
                                tempInps[i].inputs[0] = Nand([None,None])
                        else:
                            if numGates < n:
                                numGates +=1
                                tempInps[i].inputs[0] = Nand([None])

                else:
                    if(tempInps[i].inputs[0] == None):
                        if(random.randint(0,100) > 50):
                            if numGates < n:
                                numGates +=1
                                tempInps[i].inputs[0] = Nand([None,None])
                        else:
                            if numGates < n:
                                numGates +=1
                                tempInps[i].inputs[0] = Nand([None])
                    if(tempInps[i].inputs[1] == None):
                        if(random.randint(0,100) > 50):
                            if numGates < n:
                                numGates +=1
                                tempInps[i].inputs[1] = Nand([None,None])
                        else:
                            if numGates < n:
                                numGates +=1
                                tempInps[i].inputs[1] = Nand([None])
            else:
                for w in range(len(tempInps[i].inputs)):
                    if tempInps[i].inputs[w] == None:
                        choice = random.randint(0,100)
                        if(choice < 25):
                            if(choice < 18 or len(inps) < 1):
                                inps.append((str(len(inps)),Const(True,str(len(inps)))))
                                #print(len(inps)," LEN IMPORT")
                                tempInps[i].inputs[w] = inps[-1][1]
                            else:
                                tempInps[i].inputs[w] = inps[random.randint(0,len(inps) - 1)][1]
                        if(25 <= choice < 50 and numGates < n):
                            placedGate = True
                            numGates+=1
                            tempInps[i].inputs[w] = Nand([None])
                        if(50 <= choice < 101 and numGates < n):
                            placedGate = True
                            numGates+=1
                            tempInps[i].inputs[w] = Nand([None,None])
                        else:
                            tempInps[i].inputs[w] = None

    tempInps = []
    collectInputGates(root, tempInps)
    for input in tempInps:
        for i in range(len(input.inputs)):
            if(input.inputs[i] == None):
                choice = random.randint(0,25)
                if(choice < 18 or len(inps) < 1):
                    inps.append((str(len(inps)),Const(True,str(len(inps)))))
                    input.inputs[i] = inps[-1][1]
                else:
                    input.inputs[i] = inps[random.randint(0,len(inps) - 1)][1]
    #printCircuit(root)
    return root




inps = [("a",Const(True, "a")),("b",Const(True, "b")),("c",Const(True, "c"))]
root2 = Nand([inps[0][1],inps[0][1]])
root1 = Nand([root2,Nand([Nand([Nand([inps[0][1],inps[0][1]]),inps[1][1]]),Nand([inps[2][1],inps[0][1]])])])

printCircuit(root1)
rootA = Facts()
rootA.facts.append((root1, True))

#print(checkFinnished(rootA))
start = time.perf_counter()
recursiveBuildSatisfactionTree(rootA,[0],[0])
end = time.perf_counter()
print(end - start)

#(rootA.branch.left)
#print(rootA.branch.right)
printTree(rootA)
leaves = []
collectLeaves(rootA, leaves)
print(leaves)
clearContradictingLeaves(leaves)
print(leaves)
removeDuplicateFacts(leaves)
print(leaves)
orderFacts(leaves)
print(leaves)
print("GENERATED BY TREE:")
print(sorted(generateSatisfiers(leaves,inps)),"\n\n")
bruteForce = []
i = 0

while i < 2**len(inps):
    temp = bin(i)[2:]
    temp ="0" * (len(inps) - len(temp)) + temp

    for j in range(len(inps)):
        if temp[j] == "1":
            inps[j][1].setValue(True)
        else:
            inps[j][1].setValue(False)
    if root1.evaluate():
        bruteForce.append(temp)
    i+=1

print("BRUTE FORCE RESULTS:")
print(sorted(bruteForce))
print(sorted(bruteForce) == sorted(generateSatisfiers(leaves,inps)))
gates = []
times = {}

branchct = {}
opAccum = {}
print("TEST START")
print(datetime.datetime.now())
for k in range(1):
    for i in range(1,20,1):
        #Apply steps to extract satisfying states
        n = i
        assignedInps = [0]
        inpNum = 1
        baseInputs = []
        rootTest = improvedNandCircuitBuilder(n,baseInputs)#buildRandomNGateNandCircuit(n,assignedInps,baseInputs)
        testSat = Facts()
        testSat.facts.append((rootTest, True))
        start = time.perf_counter()
        numBranches = [0]
        opCount = [0]
        recursiveBuildSatisfactionTree(testSat,numBranches,opCount)
        end =  time.perf_counter()
        leaves = []
        tInps = []
        for inp in baseInputs:
            tInps.append((inp[0],inp[1]))
        collectLeaves(testSat, leaves)
        clearContradictingLeaves(leaves)
        removeDuplicateFacts(leaves)
        orderFacts(leaves)
        branchct[i] = branchct.get(i,0) + numBranches[0]
        opAccum[i] = opAccum.get(i,0) + opCount[0]



        res= sorted(generateSatisfiers(leaves,tInps))


        bruteForce = []
        h = 0
#Brute force for correct answer
        start2 = time.perf_counter()
        while h < 2**len(tInps):
            temp = bin(h)[2:]
            temp ="0" * (len(tInps) - len(temp)) + temp
            for j in range(len(tInps)):
                if temp[j] == "1":
                    tInps[j][1].setValue(True)
                else:
                    tInps[j][1].setValue(False)
            if rootTest.evaluate():
                bruteForce.append(temp)
                #print(temp)
                #print(root1.evaluate() ,"\n")
            h+=1
        end2 = time.perf_counter()
#Make sure the alg doesnt suck
        if(end2-start2 < end - start):
            print("SLOWER THAN BRUTE FORCE")

        if res != bruteForce:
            print("WRONG RESULT")


        times[i] = times.get(i,0) + (end - start)
        if(k == 0):
            gates.append(i)

print("TEST END")
print(datetime.datetime.now())

#Plot data and print data
rtimes = []
for key in sorted(times.keys()):
    rtimes.append(times[key] / 10)
print(rtimes)
print(gates)


plt.scatter(gates, rtimes)
#plt.scatter(gates[int(len(gates)/7):-1 * int(len(gates)/8)], rtimes[int(len(gates)/8):-1 * int(len(gates)/7)])
#print(np.poly1d(np.polyfit(gates, rtimes, 6)))
#plt.plot(np.unique(gates), np.poly1d(np.polyfit(gates, rtimes, 6))(np.unique(gates)))
plt.xscale('log')
plt.yscale("log")
plt.xlabel('NANDS')
plt.ylabel('COMP TIME')
plt.show()
ropAccum = []
rbranchct = []

for key in sorted(opAccum.keys()):
    ropAccum.append(opAccum[key] / 10)
plt.scatter(gates, ropAccum)

plt.xscale('log')
plt.yscale("log")
plt.xlabel('NANDS')
plt.ylabel('OPS')
plt.show()
print("NOT LOG")
for i in range(len(gates)):
    print(gates[i])
print("\n\n\n\n\n")
for i in range(len(gates)):
    print(rtimes[i])
print("LOG")
for i in range(len(gates)):
    print(math.log(gates[i]))
print("\n\n\n\n\n")
for i in range(len(gates)):
    print(math.log(rtimes[i]))

print("OPS")
for i in range(len(gates)):
    print(gates[i])
print("\n\n\n\n\n")
for i in range(len(gates)):
    print(math.log(ropAccum[i]))
