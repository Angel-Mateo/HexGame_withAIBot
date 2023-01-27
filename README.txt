====================================================================================================
- This script is a basic implementation of the Hex Game, being the gameplay terminal-based. It's part of
the final project of a series of courses on C++.

- This is an improved version of my older project. Now, a bot AI opponent has been implemented by
using Monte Carlo's algorithm.
****************************************************************************************************
(Notice that this is a basic implementation and therefore many improvements can still be done)
* If the bot opponent is used, the user should choose a board size less or equal than
7 x 7 (at least for the moment), because the algorithm hasn't been optimized yet and the computational
cost is high)
****************************************************************************************************

- Hex is a tic-tac-toe style game which consists in taking turns to try to connect the two borders
of a board of hexagonal tiles. One player must try to connect the top and bottom borders and the other
one must do the same with the lateral borders. Each player must try to connect their borders and block
the opponent's paths at the same time. The first player to connect their two borders wins.
There's an extra rule: the second player can swap if he/she wishes so, that is, take over the first
movement of the first player to avoid unfair advantage.

If you didn't know Hex and want further information, you can visit:
https://en.wikipedia.org/wiki/Hex_(board_game)
====================================================================================================

====================================================================================================
HOW TO RUN THE PROGRAM: just compile and run the script Hex_Game.cpp. The terminal prompts will
guide you in the settings process and will manage the game flow.
**** If the bot opponent is used, the user should choose a board size less or equal than
7 x 7 (at least for the moment), because the algorithm hasn't been optimized yet and the computational
cost is high) ****
====================================================================================================

====================================================================================================
Example of an 11 x 11 Hex board, as it would be drawn in this program:

      x   x   x   x   x   x   x   x   x   x   x
      0   1   2   3   4   5   6   7   8   9  10
o  0  . - . - X - . - . - . - . - X - . - . - .  0  o
       \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
  o  1  . - X - . - . - O - O - O - X - . - . - .  1  o
         \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
    o  2  . - X - X - O - . - . - O - O - O - O - .  2  o
           \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
      o  3  X - O - O - X - O - . - . - . - . - O - O  3  o
             \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
        o  4  X - O - O - X - X - X - X - . - . - . - .  4  o
               \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
          o  5  O - O - . - . - . - . - X - . - . - . - .  5  o
                 \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
            o  6  . - . - . - . - . - . - X - . - . - . - .  6  o
                   \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
              o  7  . - . - . - . - . - X - X - . - . - . - .  7  o
                     \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
                o  8  . - . - . - . - . - . - . - . - . - . - .  8  o
                       \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
                  o  9  . - . - . - . - . - . - . - . - . - . - .  9  o
                         \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
                    o 10  . - . - . - . - . - . - . - . - . - . - . 10  o
                          0   1   2   3   4   5   6   7   8   9  10
                          x   x   x   x   x   x   x   x   x   x   x
====================================================================================================
