
connectives = ["~", "^", "⌄", "->", "<->"] 
vars = ["P", "Q", "R"]
matchingBrackets = {"(": ")", "{": "}", "[": "]"}  
firstVar = []
secondVar = []
thirdVar = []
negationFirstVar = [] 
negationSecondVar = []
negationThirdVar= []

rowCount = 0
valid = True  # Glinobal ko kase para same sa lahat na ng fucking functions

# Flag to check if P Q R is negated
negateP = False 
negateQ = False
negateR = False

def userInput():
    statement = input("Enter a statement: ").upper()
    words = statement.split()
    checkParentheses(words)
    syntaxChecker(words)

def checkParentheses(words):
    global valid  # Idineclare ko para mamodify dito sa function yung tang-inang global var na yon
    stackParentheses = []  
    for word in words: 
        if word in matchingBrackets.keys():  
            stackParentheses.append(word)  
        elif word in matchingBrackets.values():  
            if stackParentheses and matchingBrackets[stackParentheses[-1]] == word:  
                stackParentheses.pop()  
            else:
                print("Invalid Statement: Unmatched closing parenthesis") 
                valid = False
                return False  

    if not stackParentheses:  
        print("Parentheses are balanced.")
    else:
        print("Parentheses are not balanced.")
        valid = False

def syntaxChecker(words):
    global valid, negateP, negateQ, negateR
    variables = [] # pagstore'n t variables nga nausar
    connectivesUsed = [] #pagstore'n t connectives nga nausar
    negationStack = [] #pagstore'n t negation nga nausar
    parenthesesUsed = [] #pagstore'n t parentheses nga nausar
    
    # Syntax check for variables, connectives, and parentheses
    for word in words:
        if word.isalpha() and word in vars:  
            variables.append(word)
            if negationStack and negationStack[-1]:
                if word == "P":
                    negateP = True
                elif word == "Q":
                    negateQ = True
                elif word == "R":
                    negateR = True
                negationStack.pop() 
        elif word in connectives: 
            connectivesUsed.append(word)
            if word == "~":
                negationStack.append(True)
        elif word in matchingBrackets.keys() or word in matchingBrackets.values():
            parenthesesUsed.append(word)
        else:
            print("Invalid syntax detected.")
            valid = False
            return

    #To check syntax din by Basilio
    for word1, word2 in zip(words, words[1:]):
        if word1 in vars and word2 in vars:
            print("Invalid Statement: Two variables cannot be adjacent.")
            valid = False
            return
        if word1 in connectives and word2 in connectives and word2 != "~":
            print("Invalid Statement: Two connectives cannot be adjacent.")
            valid = False
            return
        if words[-1] in connectives:
            print("Invalid Statement: The last word cannot be a connective.")
            valid = False
            return
        if words[0] in connectives and words[0] != "~":
            print("Invalid Statement: The first word cannot be a connective.")
            valid = False
            return

    if valid:
        uniqueVars = set(variables)  # set function para iremove yung duplicates na vars
        varPopulator(uniqueVars)  # ipopulate ang var based sa count ng unique vars to compute the rows
        readLogic(variables, connectivesUsed)

def varPopulator(uniqueVars):
    n = len(uniqueVars)  # exponent determiner base sa uniq na variable kanina
    global rowCount 
    
    # Clear the lists to avoid previous runs affecting the results
    firstVar.clear()
    secondVar.clear()
    thirdVar.clear()
    negationFirstVar.clear()
    negationSecondVar.clear()
    negationThirdVar.clear()

    rowCount = 2 ** n    # Number ng row sa truth table...tama tong formula dbaaaaaaaa 2^n?

    if n == 3:
        for i in range(rowCount): # alam niyo na to from 0 to 7 kung n = 3 and rowCount is 8
            firstVar.append("True" if (i // 4) % 2 == 0 else "False")  # nakafloor division yan ha...ieevaluate lang kung true or false tas iaappend sa first var and same din sa iba 
            secondVar.append("True" if (i // 2) % 2 == 0 else "False") # wag ko na explain ha, alam kong magaling kayo
            thirdVar.append("True" if i % 2 == 0 else "False")      

    elif n == 2:
        for i in range(rowCount):
            firstVar.append("True" if (i // 2) % 2 == 0 else "False") 
            secondVar.append("True" if (i % 2) == 0 else "False") 

    elif n == 1: #prinepare ko na to para sa mga kupal na mag-eenter ng p and not p etc
        for i in range(rowCount):
            firstVar.append("True" if (i % 2) == 0 else "False")  

    calculateNegations()

def calculateNegations():
    global negationFirstVar, negationSecondVar, negationThirdVar
    # If P is negated, create a list of the opposite values of P (True becomes False and vice versa) same for Q and R. basta awaten u lattan
    negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP else []
    negationSecondVar = ["False" if temp == "True" else "True" for temp in secondVar] if negateQ else []
    negationThirdVar = ["False" if temp == "True" else "True" for temp in thirdVar] if negateR else []

def readLogic(variables, connectivesUsed):

    print("Test")
    # conCount = 0
    # varCount = 0
    # while varCount < len(variables) or conCount < len(connectivesUsed):
    #     if conCount < len(connectivesUsed) and connectivesUsed[conCount] == "not":
    #         print(connectivesUsed[conCount] + " " + variables[varCount])
    #         conCount += 1
    #         varCount += 1
    #     elif varCount < len(variables) and varCount <= conCount:
    #         print(variables[varCount] + " ")
    #         varCount += 1
    #     if conCount < len(connectivesUsed):
    #         print(connectivesUsed[conCount] + " ")
    #         conCount += 1

def printFuckingTable():    
    if rowCount == 8:
        print(f"{'P':<10} {'Q':<10} {'R':<10}", end = "")  # string formatting based kay w3schools 
        if negateP:
            print(f"{'~P':<10}", end = "")
        if negateQ:
            print(f"{'~Q':<10}", end = "")
        if negateR:
            print(f"{'~R':<10}", end = "")
        print()
        print('-' * (30 + 10 * (negateP + negateQ + negateR))) 
        for i in range(len(firstVar)):
            print(f"{firstVar[i]:<10} {secondVar[i]:<10} {thirdVar[i]:<10}", end = "")
            if negateP:
                print(f"{negationFirstVar[i]:<10}", end = "")
            if negateQ:
                print(f"{negationSecondVar[i]:<10}", end = "")
            if negateR:
                print(f"{negationThirdVar[i]:<10}", end = "")
            print()

    elif rowCount == 4:
        print(f"{'P':<10} {'Q':<10}", end= "") 
        if negateP:
            print(f"{'~P':<10}", end = "")
        if negateQ:
            print(f"{'~Q':<10}", end = "")
        print()
        print('-' * (20 + 10 * (negateP + negateQ)))
        for i in range(len(firstVar)):
            print(f"{firstVar[i]:<10} {secondVar[i]:<10}", end = "")
            if negateP:
                print(f"{negationFirstVar[i]:<10}", end = "")
            if negateQ:
                print(f"{negationSecondVar[i]:<10}", end = "")
            print()

    elif rowCount == 2:
        print(f"{'P':<10}", end = "")
        if negateP:
            print(f"{'~P':<10}", end = "") 
        print()
        print('-' * (10 + 10 * (negateP)))
        for i in range(len(firstVar)):
            print(f"{firstVar[i]:<10}", end = "")
            if negateP:
                print(f"{negationFirstVar[i]:<10}", end = "")
            print()

# Entry point ng putang-inang user
userInput()
printFuckingTable()
