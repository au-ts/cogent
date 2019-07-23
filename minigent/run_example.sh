#!/bin/bash
stack exec minigent-exe -- tc --dump-stdout tc examples/$1/in.minigent
