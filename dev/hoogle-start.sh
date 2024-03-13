#!/usr/bin/env zsh

echo "Once the hoogle server is up, connect to it at:"
echo "http://localhost:8080"

# Meant to be run from the root of the project repository.
hoogle server --local -p 8080
