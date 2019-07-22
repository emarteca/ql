#!/bin/bash

find . -name '*.csv' -exec tail -n +2 {} \; > merged_data.out
