#!/bin/sh

git clone git@github.com:interledger/rfcs.git --branch gh-pages --single-branch web
cp -r ????-* web
cd web
git add --all
git commit -m 'chore: update gh-pages'
git push
