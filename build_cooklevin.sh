#!/bin/bash

git clone https://github.com/uds-psl/cook-levin.git
pushd cook-levin
    make deps
    make all
popd
