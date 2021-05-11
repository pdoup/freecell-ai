'''
Author: Panagiotis Doupidis
A.M.  : dai18026
Date: 22/4/2020
_________________________________________________________________

IMPORTANT! * Python 3.3+ is required. *
                        

_______________________|FREECELL SOLVER|_________________________

-Method Used: 
Accepted methods are {breadth, depth, best, astar}
_________________________________________________________________

-Input File:
.txt file including the initial state of the board.
Cards must begin from 1 for the program to function properly.
_________________________________________________________________

-Output File:
A new .txt file will be created containing the total number 
of moves to reach the solution and a short description of 
each move i.e. foundation S1, stack D3 S4 etc
_________________________________________________________________

-How to execute program from the command line:

Windows: python freecell.py <method> <input file> <output file>
Linux  : python3 freecell.py <method> <input file> <output file>

Example: python freecell.py astar board13.txt board13solution.txt
_________________________________________________________________
'''

import sys
import copy
import time
import heapq

from collections import deque

''' 
DON'T change the value of this variable!
The Program detects the max value of the deck of cards 
and assigns that Value to this variable
'''
MAX_CARD = None


def print_use():
    print('Usage: python freecell.py <method> <infile> <outfile>')
    sys.exit(-1)


# Class to handle reading/writing from/to files
class FileIO:

    def __init__(self):
        pass

    @staticmethod
    def read_file(filename: str):
        initial_stack = []

        def check_zeros_or_find_max(l_ : list):
            global MAX_CARD

            flatten = [int(j[1:]) for i in l_ for j in i]
            if 0 in flatten:
                raise RuntimeError('Error: Found 0 in initial stack!!! First card must start from 1')
            else:
                MAX_CARD = max(flatten) 

        with open(filename, 'r') as infile:
            try:
                for line in infile:
                    initial_stack.append(line.strip().split())
                # Finds the maximum value of cards in the deck or terminate if zero is found 
                check_zeros_or_find_max(initial_stack)
                # Return the initial board if no zeros were found
                return initial_stack
            except IOError as e:
                raise e

    @staticmethod
    def write_to_file(path: list, filename: str):
        with open(filename, 'w') as outfile:
            try:
                outfile.write(str(len(path))+'\n')
                outfile.write('\n'.join(move for move in path))
                print('Solution written to file {}'.format(filename))
            except IOError as e:
                raise e


'''
Class to model the input file as a freecell problem so that the initial state
is a tuple like ([[D1,S1],[H2,D3]...], [0,0,0,0], [[],[],[],[]])
First item [[D1,S1],[H2,D3]...] is the board read from the input file 
represented as a list of lists.
Second item [0,0,0,0] are the freecells that are empty initially
Third item [[],[],[],[]] are the foundations that are also empty initially
'''
class Board:

    def __init__(self, board):
        self.board = tuple(board)
        self.stacks = board[0]
        self.freecells = board[1]
        self.foundations = board[2]

    def __str__(self):
        return '{}'.format(self.board)

    # Sorts the stacks, freecells and foundations to avoid duplicates
    def __key(self):
        t_stacks = tuple(tuple(s) for s in self.stacks if s!=[])
        st_stacks = tuple(sorted(t_stacks, key=lambda item:item[-1]))
        t_freecells = tuple(filter(lambda item:item!=0, self.freecells))
        st_freecells = tuple(sorted(t_freecells, key=lambda item:item[:]))
        t_foundations = tuple(tuple(f) for f in self.foundations)
        return (st_stacks, st_freecells, t_foundations)

    def __hash__(self):
        return hash(self.__key())

    def __eq__(self, other):
        return isinstance(other, self.__class__) and self.__key()==other.__key()

    @classmethod
    def new_board(cls, board):
        return Board(copy.deepcopy(board))
    
    '''
    Find if the card is present in either stacks or freecells
    @params: card (i.e. S3)
    @return: tuple containing information concerning its place on the board
             and the index of where it was found  
    '''
    def card_index(self, card):
        if card in self.freecells:
            return ('freecells', self.freecells.index(card))
        else:
            return ('stacks', next((i for i,stack in enumerate(self.stacks) if card in stack),None))

    # Searches and removes the card from stacks or freecells pile
    def remove(self, card):
        (place, idx) = self.card_index(card)
        if place=='freecells':
            self.freecells[idx]=0
        else:
            self.stacks[idx].pop()

    @staticmethod
    def move_to_stack_requirements(card, other_card):
        suit, other_suit, value, other_value = 1 if card[0] in ('H','D') else 0,\
                1 if other_card[0] in ('H','D') else 0,int(card[1:]),int(other_card[1:])

        if suit==other_suit:
            return False
        elif suit!=other_suit and value==other_value-1:
            return True
        else:
            return False
    
    def goal(self):
        done = 0
        for idx,suit in zip(range(4),('H','D','S','C')):
            if self.foundations[idx] and self.foundations[idx][-1]==suit+str(MAX_CARD):
                done+=1
        return True if done==4 else False

    # Returns next empty index in the freecells
    def move_to_freecell(self, card):
        return next((idx for idx,val in enumerate(self.freecells) if not val),None)

    # Checks if card is eligible to move to foundations
    def move_to_foundation(self, card):
        suit,value=card[0],int(card[1:])
        if suit=='H':
            if ((value==1 and not self.foundations[0]) or 
                    (self.foundations[0] and value==int(self.foundations[0][-1][1:])+1)):
                return 0
        elif suit=='D':
            if ((value==1 and not self.foundations[1]) or 
                    (self.foundations[1] and value==int(self.foundations[1][-1][1:])+1)):
                return 1
        elif suit=='S':
            if ((value==1 and not self.foundations[2]) or 
                    (self.foundations[2] and value==int(self.foundations[2][-1][1:])+1)):
                return 2
        elif suit=='C':
            if ((value==1 and not self.foundations[3]) or 
                    (self.foundations[3] and value==int(self.foundations[3][-1][1:])+1)):
                return 3

    # Returns the indexes of all the stacks that the card can be moved to
    def move_to_stack(self, card):
        yield from (idx for idx,stack in enumerate(self.stacks) if stack and 
                    self.move_to_stack_requirements(card,stack[-1]) or not stack)

    '''
    @params: card
    @return: a list of tuples of all the moves possible done for this card.If no move can
             be achieved it returns the same board.
    '''
    def move(self, card):

        foundation_idx, freecell_idx, stack_idx = self.move_to_foundation(card),\
                    self.move_to_freecell(card),[idx for idx in self.move_to_stack(card)]
        if foundation_idx in (range(4)):
            new_board = [Board.new_board(self.board), None]
            new_board[0].remove(card)
            new_board[0].foundations[foundation_idx].append(card)
            new_board[1] = 'foundation {}'.format(card)
            return [tuple(new_board)]

        if stack_idx:
            new_boards = [[Board.new_board(self.board), None]for j in range(len(stack_idx))]
            for idx,new_board in zip(stack_idx,new_boards):
                new_board[0].remove(card)
                new_board[0].stacks[idx].append(card)
                new_board[1] = 'newstack {}'.format(card) if not self.stacks[idx] else\
                         'stack {0} {1}'.format(card, self.stacks[idx][-1])
            return [tuple(new_board) for new_board in new_boards]
        
        if freecell_idx in range(4):
            new_board = [Board.new_board(self.board), None]
            new_board[0].remove(card)
            new_board[0].freecells[freecell_idx]=card
            new_board[1] = 'freecell {}'.format(card)
            return [tuple(new_board)]

        return [(Board.new_board(self.board),None)]

    '''
    Checks all the possible cards that can be moved to another stack or freecell or foundation
    @return: a list of lists of tuples of all the moves done based on that card
    '''
    def _children(self):
        if not all(not s for s in self.stacks):
            cards_to_move = tuple(list(list(zip(*[reversed(card) for card in self.stacks if card]))[0])+\
                            list([card for card in self.freecells if card]))
        else:
            cards_to_move = tuple([card for card in self.freecells if card])

        yield from [self.move(card) for card in cards_to_move]

'''
Breadth first search Algorithm

Utilizes efficent data structures like deque and set that provide 
O(1) time complexity for search/append/pop operations
'''
class BFS:

    def __init__(self, start_board):
        self.start_board = start_board
        self.visited = set()
        self.nodes_visited = 0


    def search(self):
        # initialize queue with the start board and an empty list to keep the moves
        queue = deque([(self.start_board, [])])
        
        while queue:
            # Pop the first element in the queue
            (state,path) = queue.popleft()
            self.nodes_visited += 1

            # Traverse all the children of the popped node and add them to the queue
            # and the visited if they're not found in the visited set or are not goal.
            # If children node is goal - stop and return the moves to get there
            for children in state._children():
                for node, move in children:
                    if node in self.visited:
                        continue
                    if node.goal():
                        print('Solved!', node)
                        #print('Total nodes visited: {}'.format(self.nodes_visited))
                        yield path+[move]
                    else:
                        queue.append((node, path + [move]))
                        self.visited.add(node)


'''
Depth First Search

Recursive algorithm that expands each node until no further move can be made
'''
class DFS:

    def __init__(self, start_board):
        self.start_board = start_board
        self.nodes_visited = 0
        self.visited = deque([])

    # Recursive function to find and extend node until a solution is found
    # if node is not in the visited list.Returns the path to the solution.
    def search(self, state=None, path=None):
        self.nodes_visited+=1
        self.visited+=[state]

        if not state and not path:
            state, path = self.start_board, []

        if state.goal():
            print('Solved!', state)
            yield path

        for children in state._children():
            for node, move in children:
                if node not in self.visited:
                    yield from self.search(node, path+[move])


#==================================================#
'''
Implementation of a heuristic function to determine the state of
the board that could potentially get us closer to the solution.
This function is based on three separate factors
1) Number of empty freecells 
2) Number of cards currently in foundations
3) Number of empty stacks

After these calculations it adds weights to each one of these numbers
to signify their importance.For example the number of cards in the
foundations is the most important indicator thus it is multipiled by 60,
then the empty stacks and freecells are multipiled by 30 and 10 respectively

@params: Board
@return: Value that represents the score of that state of the Board 
'''
def heuristic_function(board: Board):
    empty_freecells=board.freecells.count(0)
    cards_in_foundations=sum([len([sublist for sublist in each_foundation])\
                                 for each_foundation in board.foundations])
    empty_stacks=sum([not stack for stack in board.stacks])

    return cards_in_foundations*60+empty_stacks*30+empty_freecells*10

'''
Priority queue to keep track and sort Boards based on
their heurustic value. 
This implementation is taken from:
https://github.com/EthanWelsh/Peg-Solitaire/blob/master/priority_queue.py
Minor tweaks were made to fit the needs of this particular problem.
'''
class PriorityQueue:

    class BoardPathPair:
        def __init__(self, board, path, score):
            self.board = board
            self.path = path
            self.value = score

        def __lt__(self, other):
            return self.value > other.value


    def __init__(self, heuristic):
        self.heap = []
        self.heuristic = heuristic
    
    def get(self):
        board_path = heapq.heappop(self.heap)
        return board_path.board, board_path.path

    def empty(self):
        return len(self.heap)==0

    def __len__(self):
        return len(self.heap)


class PQAstar(PriorityQueue):
    def __init__(self, heuristic):
        super().__init__(heuristic)

    def put(self, board_path: tuple):
        board, path = board_path
        heapq.heappush(self.heap, \
            PriorityQueue.BoardPathPair(board, path, self.heuristic(board)+len(path)))


class PQBestFirst(PriorityQueue):
    def __init__(self, heuristic):
        super().__init__(heuristic)

    def put(self, board_path: tuple):
        board, path = board_path
        heapq.heappush(self.heap, \
            PriorityQueue.BoardPathPair(board, path, self.heuristic(board)))
#================================================#

'''
Best-First Search algorithm

Uses the same principle as the BFS but instead of a normal
queue it utilizes the PriorityQueue (PQBestFirst) above to rank each node
and place it accordingly in the queue.
'''
class BestFirst:
    def __init__(self, start_board, heuristic):
        self.start_board = start_board
        self.heuristic = heuristic
        self.visited = set()
        self.nodes_visited = 0

    def search(self):
        queue = PQBestFirst(self.heuristic)
        queue.put((self.start_board, []))

        while not queue.empty():
            state,path=queue.get() 
            self.nodes_visited+=1

            if state.goal():
                #print('Solved!', node)
                #print('Total nodes visited: {}'.format(self.nodes_visited))
                yield path

            for children in state._children():
                for node, move in children:
                    if node in self.visited:
                        continue
                    queue.put((node, path+[move]))
                    #print(node)
                    self.visited.add(node)


'''
A* Search algorithm

Identical to the Best-First Search with the exception of 
the PriorityQueue (PQAstar) which takes into account not only
the path to the goal but also the length of the path to get to that node
'''
class AStar:
    def __init__(self, start_board, heuristic):
        self.start_board = start_board
        self.heuristic = heuristic
        self.visited = set()
        self.nodes_visited = 0

    def search(self):
        queue = PQAstar(self.heuristic)
        queue.put((self.start_board, []))

        while not queue.empty():
            state,path=queue.get() 
            self.nodes_visited+=1

            if state.goal():
                #print('Solved!', node)
                #print('Total nodes visited: {}'.format(self.nodes_visited))
                yield path

            for children in state._children():
                for node, move in children:
                    if node in self.visited:
                        continue
                    queue.put((node, path+[move]))
                    #print(node)
                    self.visited.add(node)


def main():

    if len(sys.argv[1:])!=3:
        print_use()
    else:
        method, infile, outfile = (sys.argv[i] for i in range(1,4))
        start_stack = FileIO.read_file(infile)
        start_freecells = 4*[0]
        start_foundations = [[] for j in range(4)]
        start_board = Board((start_stack, start_freecells, start_foundations))
    
    start = time.time()    
    
    if method=='breadth':
        seeker = BFS(start_board)
        try:
            path = next(seeker.search())
        except StopIteration:
            path = 0
        
        if path:
            FileIO.write_to_file(path, outfile)
        else:
            print('No solution found')

    elif method=='depth':
        seeker = DFS(start_board)
        try:
            path = next(seeker.search())
        except StopIteration:
            path = 0
        
        if path:
            FileIO.write_to_file(path, outfile)
        else:
            print('No solution found')

    elif method=='astar':
        seeker = AStar(start_board, heuristic_function)
        try:
            path = next(seeker.search())
        except StopIteration:
            path = 0
        
        if path:
            FileIO.write_to_file(path, outfile)
        else:
            print('No solution found')
    
    elif method=='best':
        seeker = BestFirst(start_board, heuristic_function)
        try:
            path = next(seeker.search())
        except StopIteration:
            path = 0
        
        if path:
            FileIO.write_to_file(path, outfile)
        else:
            print('No solution found')
    else:
        print('Enter a valid method {breadth, depth, astar, best}')
        sys.exit(1)

    print('Time taken: {}s'.format(str(time.time()-start)[:5]))
    
if __name__ == '__main__':
    main()
