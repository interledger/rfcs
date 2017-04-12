'use strict'

const fs = require('fs')
const path = require('path')
const viz = require('viz.js')

const dotFile = path.resolve(__dirname, './assets/model.dot')
const svgFile = path.resolve(__dirname, './assets/model.svg')

const dotData = fs.readFileSync(dotFile, 'utf8')
const svgData = viz(dotData)
fs.writeFileSync(svgFile, svgData, 'utf8')
