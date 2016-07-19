'use strict'

const fs = require('fs')
const path = require('path')
const viz = require('viz.js')

const buildGraph = (graph) => {
  const dotFile = path.resolve(__dirname, graph + '.dot')
  const svgFile = path.resolve(__dirname, graph + '.svg')

  const dotData = fs.readFileSync(dotFile, 'utf8')
  const svgData = viz(dotData)
  fs.writeFileSync(svgFile, svgData, 'utf8')
}

buildGraph('../shared/graphs/interledger-model')
buildGraph('../shared/graphs/transfer-states')
