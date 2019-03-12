#!/bin/bash

# Sanity checks for source files in directory [src].

ML_FILES=`find ./src -name "*.ml"`

awk 'length>78 {print FILENAME ", line " FNR ": more than 78 characters..."}' $ML_FILES
awk '/.*\s$/   {print FILENAME ", line " FNR ": trailing spaces..."}        ' $ML_FILES
awk '/.*\t.*/  {print FILENAME ", line " FNR ": contains tabs..."}          ' $ML_FILES

# Sanity checks for PML files in directories [lib] and [examples].

PML_FILES=`find ./lib ./examples -name "*.pml"`

awk 'length>78 {print FILENAME ", line " FNR ": more than 78 characters..."}' $PML_FILES
awk '/.*\s$/   {print FILENAME ", line " FNR ": trailing spaces..."}        ' $PML_FILES
awk '/.*\t.*/  {print FILENAME ", line " FNR ": contains tabs..."}          ' $PML_FILES

# Check for issue number of FIXMEs and TODOs in source files and PML files.

FILES=`find ./src -name "*.ml" && find ./lib ./examples ./tests -name "*.pml"`

awk '/FIXME [^#]/ {print FILENAME ", line " FNR ": FIXME without issue number"}' $FILES
awk '/TODO [^#]/  {print FILENAME ", line " FNR ": TODO without issue number"}'  $FILES
