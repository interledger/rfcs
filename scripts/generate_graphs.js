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

for (let file of fs.readdirSync(path.resolve(__dirname, '../shared/graphs'))) {
  if (file.endsWith('.dot')) {
    buildGraph(path.resolve(__dirname, '../shared/graphs') + '/' + file.substring(0, file.length - 4))
  }
}
