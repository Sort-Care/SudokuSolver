# Usage
## Solve sudoku
```
python3 sudoku.py [number]
```
where the number should be among {1, 2, 10, 15, 25, 26, 48, 51, 62, 76, 81, 82, 90, \
95, 99, 100}. Or you can input your own full file name.

## Evaluate soduku difficulty
```
python3 sudoku.py -d [filename or puzzle number]
```

# Example
```
python3 sudoku.py 100
```
will run the sudoku solver with file ```puzzle100.txt``` as input, and the output wi\
ll be printed to the command line.
