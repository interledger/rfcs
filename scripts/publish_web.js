'use strict'

const path = require('path')
const exec = require('child_process').execSync

const cwd = path.resolve(__dirname, '../web')
const status = exec('git status --porcelain', { cwd }).toString('utf8')
if (status.length) {
  exec('git add --all', { cwd })
  exec('git commit -m \'chore: update gh-pages\'', { cwd })
  exec('git push', { cwd })
}
