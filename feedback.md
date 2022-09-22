1. Need a better method of structuring the files.
   Currently vs code doesn't play nicely with idris in .md files,
   for example, none of the idris commands are accessible in the .md file.
2. I would recommend moving the answers to a separate Answers folder to explicitly mark
   that the files contain answers to the exercises, and that you should look at them
   when you're done.
3. There's a pretty critical error to the spirit of the exercise for iso3.
   Should be ```iso3 : ToType BoolDesc1 `Iso` ToType BoolDesc2```.
