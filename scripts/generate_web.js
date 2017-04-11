'use strict'

const fs = require('fs')
const ejs = require('ejs')
const glob = require('glob')
const path = require('path')
const exec = require('child_process').execSync
const marked = require('marked')
const cheerio = require('cheerio')

// We need a custom renderer to make sure we generate the same header IDs as
// Github.
const renderer = new marked.Renderer()
renderer.heading = function (text, level, raw) {
  const candidateId = raw
    .toLowerCase()
    .replace(/[^\w\- ]+/g, '')
    .replace(/ /g, '-')

  return '<h'
  + level
  + ' id="'
  + this.options.headerPrefix
  + candidateId
  + '">'
  + text
  + '</h'
  + level
  + '>\n';
}

// Override relative links to .md files to the folder
// (Allows github to be linked properly, and website as well)
renderer.link = function (href, title, text) {
  href = href.replace(/^(\.{2}\/\d{4}-.*)\/(\d{4}-.*\.md)$/g, '$1')
  return marked.Renderer.prototype.link.call(this, href, title, text);
};

let cwd = path.resolve(__dirname, '..')
exec('rm -rf web', { cwd })
exec('git clone git@github.com:interledger/rfcs.git --branch gh-pages --single-branch web', { cwd })
exec('cp -r ????-* web', { cwd })
exec('cp -r shared web', { cwd })

const template = ejs.compile(fs.readFileSync('tmpl/rfc.ejs.html', 'utf8'))
const files = glob.sync('????-*/????-*.md')

files.forEach((file) => {
  const markdownContent = fs.readFileSync(file, 'utf8')
  const renderedMarkdown = marked(markdownContent, { renderer })
  const $ = cheerio.load(renderedMarkdown)
  const title = $('h1').text()

  // Ensure heading IDs are unique
  const idMap = new Map()
  const headings = $('h1,h2,h3,h4,h5,h6').each(function () {
    const tag = $(this)
    const id = tag.attr('id')
    let tags = idMap.get(id)
    if (!tags) {
      tags = []
      idMap.set(id, tags)
    }
    tags.push(tag)
  })

  for (let group of idMap) {
    if (group[1].length > 1) {
      group[1].forEach((tag, i) => {
        tag.attr('id', tag.attr('id') + '-' + (i + 1))
      })
    }
  }

  // Generate navigation
  const toc = $('h2, h3').map(function () {
    const tag = $(this)
    return {
      type: tag.get(0).tagName,
      title: tag.text(),
      anchor: tag.attr('id')
    }
  }).get()

  $('table').addClass('table').addClass('table-striped')

  $('p').first().addClass('intro')

  $('img').addClass('img-responsive')

  const content = $.html()

  const renderedHtml = template({ title, content, toc })

  fs.writeFileSync('web/' + path.dirname(file) + '/index.html', renderedHtml)
})

cwd = path.resolve(__dirname, '../web')
const status = exec('git status --porcelain', { cwd }).toString('utf8')
if (!status.length) {
  console.log('no changes')
} else {
  console.log(status)
}
