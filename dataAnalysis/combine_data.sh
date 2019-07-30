#!/bin/bash

# combine data without a filename included
#find . -name '*.csv' -exec tail -n +2 {} \; > merged_data.out

# combine data with the filename included
find . -name '*.csv' | xargs -I % sh -c "tail -n +2 % | sed -ne s@\\\$@,%@p" > merged_data_withFile.out
