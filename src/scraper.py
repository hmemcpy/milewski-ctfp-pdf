import os
import pypandoc
import pathlib
from requests import get
from bs4 import BeautifulSoup
from mercury_parser import ParserAPI

# get the API key at https://mercury.postlight.com/web-parser/
mercury = ParserAPI(api_key='<your API key>')

index_page = 'https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/'


def get_toc():
    result = []
    part = 0
    chapter = 0
    lists = get_content(get(index_page).content).find_all('ol')
    for part_list in lists:
        part += 1
        for li in part_list.find_all('li'):
            chapter += 1
            result.append({'chapter': '{}.{}'.format(part, chapter),
                           'title': li.a.text,
                           'url': li.a['href']})
        chapter = 0
    return result


def get_content(html):
    soup = BeautifulSoup(html, 'html.parser')
    return soup.find(class_='post-content')


def write_content(file, content):
    with file.open('w') as f: f.write(content)


def save_images(markup, path):
    import urllib.request
    html = get_content(markup)
    images = html.find_all('img')
    for img in images:
        image_url = img.parent['href']
        image_file = image_url.split('/')[-1]
        target_file = path.joinpath(image_file)
        urllib.request.urlretrieve(image_url, target_file)
        img['src'] = 'images/' + target_file.name
        img.parent.replaceWithChildren()  # removes the parent <a href...> and replaces it with the image
    return html


def save_url(chapter, title, url):
    file_name = '{}.tex'.format(title.replace('/', '\\').replace(':', ' -'))
    path = pathlib.Path(os.path.join('content', chapter, 'images'))
    path.mkdir(parents=True, exist_ok=True)

    p = mercury.parse(url)
    html = save_images(p.content, path)

    content = pypandoc.convert_text(html, 'tex', format='html')
    write_content(path.parent.joinpath(file_name), content)


for toc in get_toc():
    print(toc)
    title = toc['title']
    chapter = toc['chapter']
    url = toc['url']
    save_url(chapter, title, url)
save_url('0.0', 'Preface', index_page)
