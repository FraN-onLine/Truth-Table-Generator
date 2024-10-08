import sys
connectives = ["~", "^", "v", "->", "<->"] 
vars = ["p", "q", "r"]
matchingBrackets = {"(": ")"}  

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
      file = open("input.txt","rt")
      lines = file.readlines()
      logStatementCount = 0
      statement = []

      for line in lines:
         strippedLine = line.strip()
         if strippedLine != "":
           statement.append(strippedLine)
           logStatementCount+=1
         else:
            pass
         
      if logStatementCount < 2:
        statementToReturn = statement[0]
        return statementToReturn.lower()
      else:
         raise ValueError(f"We found {logStatementCount}, input 1 statement only")
              
    except ValueError as Ve:
        print(f"Invalid Number of Inputs: {Ve}") 
        sys.exit()
    except FileNotFoundError:
        print("File was not found")
        sys.exit()
        

def userInput():
    global variables
    subStatements = []
    # statement = statementFromFile()
    statement = input("Enter a statement: ").lower()
    words = statement.split()
    
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
    variables = []  # Store variables used
    connectivesUsed = []  # Store connectives used

    for index, word in enumerate(words):
        if word.isalpha() and word in vars:  
            variables.append(word)
        elif word in connectives: 
            connectivesUsed.append(word)
            if word == "~":
                if words[index + 1] in vars:
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
             print("Invalid Statement: Parenthesis should be separated with a space. Maybe try \"( " + " ".join(word[1:].upper())  + "\"?") #guides the user to our program's syntax
             valid = False
             return
        elif word[-1] == ")" and len(word) > 1: 
             print("Invalid Statement: Parenthesis should be separated with a space. Maybe try \"" + " ".join(word[:-1].upper())+ " )\"?") #guides the user to our program's syntax
             valid = False
             return
        elif word.isalpha():
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
        varPopulator(len(uniqueVars)) 
        return True
        
def varPopulator(n):
    global rowCount 
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

def removeParentheses(subst):

        while subst.startswith("(") and subst.endswith(")"):
            subst = subst[1:-1].strip()
        return f"( {subst} )" if subst else ""

def extractPropositions(statement):

    print(statement)
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
            
        if char.isalpha() and char != 'v':
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

    normalizedStatement = removeParentheses(statement)
    
    if normalizedStatement not in processedStatements or normalizedStatement not in subStatements:
        subStatements.append(statement) 
    return sorted(propositions), subStatements #sorted para magreturn as list yung propositions 

def evaluateStatement(subStatements, variables):
    results = [[] for _ in subStatements] #magcrecreate ng empty list for every substatements para sa mga results nila

    for i in range(rowCount): 
        if rowCount == 8:
            rowValues = {variables[0]: firstVar[i], variables[1]: secondVar[i], variables[2]: thirdVar[i]}  

        if rowCount == 4:
            rowValues= {variables[0]: firstVar[i], variables[1]: secondVar[i]}

        if rowCount == 2:
            rowValues = {variables[0]: firstVar[i]}

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
        
        subStatement = subStatement.replace("~", " not ")  
        subStatement = subStatement.replace("^", " and ")    
        subStatement = subStatement.replace("v", " or ")     
        subStatement = subStatement.replace("<->", " is ")   
        subStatement = subStatement.replace("->", " <= ") 

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

    # Print headers for truth table.
    print(" ".join([f"{header:<10}" for header in headers]), end=" ")

    # Print sub-statements in the table header.
    header = " ".join([f"{sub:<15}" for sub in subStatements])
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
        if negateP:
            row.append(f"{negationFirstVar[i]:<10}")
        if negateQ:
            row.append(f"{negationSecondVar[i]:<10}")
        if negateR:
            row.append(f"{negationThirdVar[i]:<10}")

        print(" ".join(row), end=" ")

        # Print results for each sub-statement.
        resultRow = " ".join([f"{results[j][i]:<15}" for j in range(len(subStatements))])
        print(resultRow)
        
# Entry point ng putang-inang user
userInput()
