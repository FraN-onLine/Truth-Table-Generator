import sys
import re #helps evaluating statements with multiple spaces
import os

connectives = ["~", "^", "v", "->", "<->"] # syntax for connectives used
vars = ["p", "q", "r", "T", "F"] # set of propositions and constant values which takes the place of vars when checking or computing
matchingBrackets = {"(": ")"}  
precedence = {"~": 3, "^": 2, "v": 2, "->": 1, "<->": 0}  # precedence of operators ~ being highest, <-> being lowest

openBrackets = set(matchingBrackets.keys())
closeBrackets = set(matchingBrackets.values())

firstVar = []
secondVar = []
thirdVar = []

negationFirstVar = [] 
negationSecondVar = [] 
negationThirdVar= []

variables = []

rowCount = 0
valid = True  # Glinobal ko kase para same sa lahat na ng fucking functions, (cge po)



# Flag to check if P Q R is negated
negateP = False 
negateQ = False
negateR = False


def statementFromFile():
    try:
        file = open("input.txt", "rt")
        lines = file.readlines()          
        logStatementCount = 0
        statement = []

        if os.path.getsize("input.txt") == 0:    #os.path.getsize gets the size of the input.txt file. If the file is empty, it will prompt the user to enter a statement in the terminal. Otherwise, it will create the file and write the user's input into it.  
            print("Text File is currently empty.")
            file = open("input.txt", "w")
            file.write(input("Enter statement to store in the text file: ").lower())
            file.close()
            return statementFromFile()

        for line in lines:    #It will check the content in the text file and ignore any extra spaces, ensuring that the statement is still read even if it's surrounded by spaces.
            strippedLine = line.strip()
            if strippedLine != "":
                statement.append(strippedLine)
                logStatementCount += 1

        if logStatementCount < 2:  #If there is only one statement in the text file, it will return the statement in lowercase.
            statementToReturn = statement[0]
            return statementToReturn.lower()
        else:
            raise ValueError(f"We found {logStatementCount} statements, input only 1 statement.") #If there are more than one statement in the text file, it will raise an error.

    except ValueError as Ve:     #every value error will be caught here
        print(f"Invalid number of inputs: {Ve}")
        sys.exit()

    except FileNotFoundError:     #If the file is not found, it will prompt the user to choose from the following options: 1. Make a new file 2. Provide input via console 3. End program
        print("File was not found.")
        print("Please choose from the following:")
        print("1. Make a new file\n2. Provide input via console\n3. End program")

        while True:
            try:
                inputChoice = input("Enter choice: ")

                if inputChoice == "1":
                    file = open("input.txt", "w")
                    if os.path.getsize("input.txt") == 0:
                        file.write(input("Enter a statement: ").lower())
                        file.close()
                        return statementFromFile()  #recursion so that the program will read the newly entered statement

                elif inputChoice == "2":
                    statement = input("Enter a statement: ").lower() 
                    return statement

                elif inputChoice == "3":
                    sys.exit()

                else:
                    raise ValueError("Invalid Input")    #If the user enters an invalid input, it will raise an error.
                    
            except ValueError as Ve:
                print(f"Error found: {Ve}") 
                

def injectParentheses(subStatement):
    
    output = []  # Stack for building the parenthesized expression
    operators = []  # Stack to hold operators and apply precedence
    tokens = subStatement.split()  # Tokenize the input statement

    # Helper function to handle precedence and pop from operator stack
    def applyOperator():
        op = operators.pop()
        if op == "~":
            operand = output.pop()
            if operators: # to not cause an error when we check the top of the stack
                if operators[-1] == "~": # cleans output by not adding space after the operand when we do more than one negation
                    output.append(f" {op} {operand}") #without this ~ ~ ~ ~ q will be " ~ ~ ~ ~ q    "
                else:
                    output.append(f" {op} {operand} ")
            else:
                output.append(f" {op} {operand} ")
        else:  # Binary operators
            right = output.pop()
            left = output.pop()
            output.append(f"( {left} {op} {right} )")

    # Iterate through the tokens
    for token in tokens:
        if token in vars:  # If it is a proposition, add it to output
            output.append(token)
        elif token == "~": 
            operators.append(token)  # Push '~' to operator stack
        elif token in ["^", "v", "->", "<->"]:
            while (operators and operators[-1] in connectives and #adds to operator stack if empty or has lower precedence than top most operator
                   precedence[operators[-1]] >= precedence[token]): #if the previous operator has higher or equal precedence than current operator, operate it
                applyOperator()
            operators.append(token)  # Push the current operator to the stack
        elif token == "(":
            operators.append(token)
        elif token == ")":  
            while operators and operators[-1] != "(": #follows precedence between ( and ), and brackets them 
                applyOperator() 
            operators.pop()  # Remove the left parenthesis

    # handles remaining operators from the stack
    while operators:
        applyOperator()

    # The final parenthesized expression will be in the output stack
    return output[0] if output else ""
        
def userInput():
    global variables
    subStatements = []
    statement = statementFromFile()
    #statement = input("Enter a statement: ").lower()
    statement = statement.replace("t", "T").replace("f", "F")
    
    words = statement.split()
    statement = re.sub(r'\s+', ' ', statement) #trims multiple statements using regex
    

    
    if syntaxChecker(words) and checkParentheses(words):
        variables, subStatements = extractPropositions(statement)

        print("Propositional Variables:", variables) #Print test forda variables bes same thing sa bottom
        print("Sub-statements:", subStatements)

        evaluateStatement(subStatements, variables)

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
        pass
    else:
        print("Invalid Statement: Parantheis are not balanced")
        valid = False

    if valid:
        return True
    else:
        return False

def syntaxChecker(words):
    global valid, negateP, negateQ, negateR
    variables = []  # Store variables used, this excludes T or F
    connectivesUsed = []  # Store connectives used

    for index, word in enumerate(words): #validates the syntax, checks variables and connectives
        
        if word.isalpha() and word in vars:
            if word.islower(): #islower() filters T or F and non constant variables
             variables.append(word)
             
        elif word in connectives: 
            connectivesUsed.append(word)
            if word == "~" and words[index + 1] in vars: #if the next element of a negation is a variable
                i = 1
                while words[index - i] == "~": #counts negations
                    i += 1
                if i % 2 == 1: #display it's negation if odd amount of negations
                    if words[index + 1] == "p":
                        negateP = True
                    elif words[index + 1] == "q":
                        negateQ = True
                    elif words[index + 1] == "r":
                            negateR = True
                
        elif word in matchingBrackets.keys() or word in matchingBrackets.values():
            if word in matchingBrackets.keys():
                if words[index + 1] in connectives and words[index + 1] != "~":
                    print("Invalid Statement: Connective cannot follow an Open Parenthesis.") #this solves issues like ( p ( ^ q ))
                    valid = False
                    return
                if words[index + 1] in matchingBrackets.values():
                    print("Invalid Statement: Parentheses cannot be empty.") # handles empty parentheses like ( ( ) ( p ^ q ) )
                    valid = False
                    return
            if word in matchingBrackets.values():
                if words[index - 1] in connectives:
                    print("Invalid Statement: Closed Parenthesis cannot be preceeded by a connective.") #this solves issues like ( p ^ ) q 
                    valid = False
                    return
        elif word[0] == "~" and len(word) > 1: 
             print("Invalid Statement: Negations should be separated with a space. Maybe try ~ " + " ".join(word[1:].upper()) + "?") #guides the user to our program's syntax
             valid = False
             return
        elif word[0] == "(" and len(word) > 1: 
             print("Invalid Statement: Parenthesis should be separated with a space. Maybe try \"( " + " ".join(word[1:].upper())  + " ...\"?") #guides the user to our program's syntax
             valid = False
             return
        elif word[-1] == ")" and len(word) > 1: 
             print("Invalid Statement: Parenthesis should be separated with a space. Maybe try \"... " + " ".join(word[:-1].upper())+ " )\"?") #guides the user to our program's syntax
             valid = False
             return
        elif word.isalpha() and len(word) == 1:
            print("Invalid Statement: As much as we want to accept \"" + word + "\" Please enter P, Q or R as statements only. ") #guides the user to our program's syntax
            valid = False
            return
        else:
            print("Invalid Statement: Invalid syntax detected. " + word + " not recgonized")
            valid = False
           
            return
        
    wordList = [word for word in words if word not in matchingBrackets.keys() and word not in matchingBrackets.values()]
    # copy of the list of words
    # this makes sure checking of adjacent variables and connectives will go smoothly
    # like in p -> q ( r -> r ) where q and r are adjacent
    # this allows ( ( ) ^ q ) and ( ( q ) q ) to be checked properly
    # only removes from the copy
    # also allows instances like ( ) to be marked as invalid
    
    if len(wordList) == 0:
        print("Invalid Statement: no variables or connectives detected")
        valid = False
        return
    # handles "( )" and other empty inputs
    
    if len(wordList) == 1 and wordList[0] in connectives:
        print("Invalid Statement: cannot evaluate a connective by itself")
        valid = False
        return
    # handles input that is just one connective

    # To check syntax for adjacent variables and connectives 
    for word1, word2 in zip(wordList, wordList[1:]):
        if word1 in vars and word2 in vars:
            print("Invalid Statement: Two variables cannot be adjacent.") # handles inputs like " p p ^ p "
            valid = False
            return
        if word1 in vars and word2 == "~":
            print("Invalid Statement: Negation cannot proceed a variable.") # handles inputs like " ~ p ~ q "
            valid = False
            return
        if word1 in connectives and word2 in connectives and word2 != "~":
            print("Invalid Statement: Two connectives cannot be adjacent.") #handles inputs like " p ^ v p"
            valid = False
            return
        if wordList[-1] in connectives:
            print("Invalid Statement: The last word cannot be a connective.") # handles inputs like " p ^ "
            valid = False
            return
        if wordList[0] in connectives and wordList[0] != "~":
            print("Invalid Statement: The first word cannot be a connective.") # handles inputs like " ^ p"
            valid = False
            return

    if valid:
        uniqueVars = set(variables)  # Remove duplicates from vars
        varPopulator(len(uniqueVars), uniqueVars) 
        return True
        
def varPopulator(n, uniqueVars):
    global rowCount 
    rowCount = 2 ** n    # Number ng row sa truth table...tama tong formula dbaaaaaaaa 2^n?
    if rowCount == 0:
        rowCount = 1

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
            
    

    calculateNegations(uniqueVars) #passes unique vars again to negations

def calculateNegations(uniqueVars):
    global negationFirstVar, negationSecondVar, negationThirdVar
    # If P is negated, create a list of the opposite values of P (True becomes False and vice versa) same for Q and R. basta awaten u lattan
    
    if rowCount == 8:
        #every possible proposition is present and follows this order
        negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP else []
        negationSecondVar = ["False" if temp == "True" else "True" for temp in secondVar] if negateQ else []
        negationThirdVar = ["False" if temp == "True" else "True" for temp in thirdVar] if negateR else []
        
    elif rowCount == 4: 
        if "r" in uniqueVars: 
            #first var guarantees that either exclusively P or Q if r is present, R being always the second var
            negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP or negateQ else [] 
            negationSecondVar = ["False" if temp == "True" else "True" for temp in secondVar] if negateR else []
        else: #if r is not present we know variables are P and Q
            negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP else [] 
            negationSecondVar = ["False" if temp == "True" else "True" for temp in secondVar] if negateR else []
            
    elif rowCount == 2: #if any negation is present, it's the negated first var
         negationFirstVar = ["False" if temp == "True" else "True" for temp in firstVar] if negateP or negateQ or negateR else [] 

def removeParentheses(subst):

        while subst.startswith("(") and subst.endswith(")"):
            subst = subst[1:-1].strip()
        return f"( {subst} )" if subst else ""

def extractPropositions(statement):

    statement = injectParentheses(statement) #injects parenthesis for precedence
    normalizedStatement = removeParentheses(statement) # sorts issues like ( ( ( p v q ) ) ) causing redundant calculations
    print(normalizedStatement)
    propositions = set()
    subStatements = []
    stackOpenBracket = []
    negateSubStatement = False
    checkNegatedCompound = False
    processedStatements = set()

    for index, char in enumerate(statement):
        
        if checkNegatedCompound:        # if Negation or ~ was detected, check for next element if it's parenthesis
            if statement[index] == " ":
                continue
            elif statement[index] == "(":   #if it is, negate the next substatement like ~ ( P v Q )
                negateSubStatement = True
                checkNegatedCompound = False
            else:
                checkNegatedCompound = False  #if not, it's likely a proposition like ~ P
        
        if char == "~":
            checkNegatedCompound = True #check if compound is to be negated
            
        if char.isalpha() and char != 'v' and char.islower():
            propositions.add(char)

        if char in openBrackets:
            stackOpenBracket.append((index, negateSubStatement))  # If open parentheses siya, ilalagay sa stack yung parentheses at yung index bale kung ( p v r) v q 
            negateSubStatement = False #this tracks and resets negation status to be retrieved when we reach the end of the statement
            #this fix errors later on that would happen with ~ ( p ^ ( q v r )) if this statements were not added
                                        

        elif char in closeBrackets and stackOpenBracket:
                start, wasNegated = stackOpenBracket.pop() # Retrieve the negation state at this level
                subst = statement[start : index + 1]

                normalizedSubst = removeParentheses(subst)

                if normalizedSubst not in processedStatements:
                    subStatements.append(normalizedSubst) 
                    processedStatements.add(normalizedSubst)  # Track to avoid duplicates

                    if wasNegated: #negates the substatement if there's a ~ prior to it
                        negatedSubst = "~ " + normalizedSubst
                        if negatedSubst not in processedStatements and negatedSubst != statement:
                            subStatements.append(negatedSubst)
                            processedStatements.add(negatedSubst)
                        negateSubStatement = False
    
    if normalizedStatement not in processedStatements or normalizedStatement not in subStatements:
        subStatements.append(statement) 
    return sorted(propositions), subStatements #sorted para magreturn as list yung propositions 

def evaluateStatement(subStatements, variables):
    results = [[] for _ in subStatements] #creates empty list for the results of every subStatements

    for i in range(rowCount): 
        if rowCount == 8:
            rowValues = {variables[0]: firstVar[i], variables[1]: secondVar[i], variables[2]: thirdVar[i]}  

        elif rowCount == 4:
            rowValues= {variables[0]: firstVar[i], variables[1]: secondVar[i]}

        elif rowCount == 2:
            rowValues = {variables[0]: firstVar[i]}
            
        else:
            rowValues = {} #when there's no propositions and use of T or F is only used

        for index, subStatement in enumerate(subStatements):
            evaluatedResult = evalProposition(subStatement, rowValues) 
            results[index].append(evaluatedResult)

    printFinalTable(results, subStatements, variables)

def evalProposition(subStatement, rowValues):

    try:
        
        if 'r' in rowValues:
            subStatement = subStatement.replace("r", rowValues['r'])
            # key r will be evaluated first and will be replaced by corresponding value
            # if otherwise, p and q which truth values happen to be True will have it's r be replaced with r's value
            # leading to errors such as TTrueue and TFalseue
            
        if 'p' in rowValues:
            subStatement = subStatement.replace("p", rowValues['p'])
        
        if 'q' in rowValues:
            subStatement = subStatement.replace("q", rowValues['q'])
            
        subStatement = re.sub(r"\bT\b", "True", subStatement)  # Convert standalone T to True
        subStatement = re.sub(r"\bF\b", "False", subStatement)  # Convert standalone F to False

        
        subStatement = re.sub(r'~\s*\(([^)]+)\)', r'(not (\1))', subStatement) #this is converted before simple negations
        # this regex assures that not followed by a compound statement
        # is converted to ( not ( statement ) ) fixing possible issues with implication using <= instead of not p or q
        
        subStatement = subStatement.replace("~", " not ") #replaces simple negation with not
        subStatement = subStatement.replace("^", " and ")    
        subStatement = subStatement.replace("v", " or ")     
        subStatement = subStatement.replace("<->", " is ")   
        subStatement = subStatement.replace("->", " <= ") 
        subStatement = re.sub(r"not\s+True", "False", subStatement) # implication has issues with -> ~ since True <= not True 
        subStatement = re.sub(r"not\s+False", "True", subStatement) # or vice versa cant be calculated, this cleans up negations

        return str(eval(subStatement)) #error sa boolean output try niyo nga lagyan ng try and exception para mas specific yung error diko madebug
    except Exception as e:
        return f"Error: {str(e)}"


def printFinalTable(results, subStatements, variables):

    headers = []

    if 'p' in variables:
        headers.append("p")
    if 'q' in variables:
        headers.append("q")
    if 'r' in variables:
        headers.append("r")

    if negateP:
        headers.append("~p")
    if negateQ:
        headers.append("~q")
    if negateR:
        headers.append("~r")

    # Print variable headers for truth table.
    print(" ".join([f"{header:<10}" for header in headers]), end=" ")

    # Print sub-statements in the table header.
    header = " ".join([f"{sub:<{len(sub) + 5}}" for sub in subStatements])
    print(header)

    totalWidth = 10 * len(headers) + len(header)
    print('-' * totalWidth)

    for i in range(rowCount):
        row = []
        # Print truth values for variables.
        if rowCount == 8:
            print(f"{firstVar[i]:<10} {secondVar[i]:<10} {thirdVar[i]:<10}", end=" ")
        elif rowCount == 4:
            print(f"{firstVar[i]:<10} {secondVar[i]:<10}", end=" ")
        elif rowCount == 2:
            print(f"{firstVar[i]:<10}", end=" ")
        if len(negationFirstVar) > 0:
            row.append(f"{negationFirstVar[i]:<10}")
        if len(negationSecondVar) > 0:
            row.append(f"{negationSecondVar[i]:<10}")
        if len(negationThirdVar) > 0:
            row.append(f"{negationThirdVar[i]:<10}")

        print(" ".join(row), end=" ")

        # Print results for each sub-statement.
        resultRow = " ".join([f"{results[j][i]:<{len(subStatements[j]) + 7}}" for j in range(len(subStatements))])
        print(resultRow)
        
# Entry point ng putang-inang user
userInput()
