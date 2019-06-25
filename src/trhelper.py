import re
from pathlib import Path

crit = re.compile(r'\\newcommand{\\tr')
c = re.compile(r'\\tr[a-zA-Z]+')
cc = re.compile(r'[^%]+$')
with open("preamble.tex","r",encoding='utf-8') as f:
    d = [x.strip() for x in f.readlines() if crit.match(x)]

word_list = []
for line in d:
    try:
        word_list.append((c.search(line)[0].strip(),cc.search(line)[0].strip()))
    except:
        pass

tr_list = [x[0] for x in word_list]
jargon_list = [x[1] for x in word_list]
for i in word_list:
    print(i)

def get_file_from_ch_name():
    ch = input("챕터를 입력해주세요(1.1, 3.3 등의 포맷)\r\n")
    p = Path("./content/"+ch.strip())
    for i in [x.name for x in p.iterdir()]:
        if i.endswith(".tex"):
            name = i
    try:
        return "./content/"+ch.strip()+"/"+name
    except NameError:
        raise NameError("Invalid chapter name")

def one():
    print("!!주의!! 본 작업은 롤백이 안 됩니다.")
    print("또한, 작업을 2번 실행하시게 되면 \\tr\\trCategory 같은 꼴의 무언가가 생깁니다.")
    print("\\newcommand{\\tr~~~}{(용어)} % ~~ 포맷을 가지고 돌아가는 프로그램입니다.")
    print("주석을 제대로 쓰셨는지 다시 한 번 확인 부탁드립니다.")
    name = get_file_from_ch_name()
    with open(name,"r",encoding='utf-8') as f:
        d = f.read()
    for tr,word in word_list:
        d = d.replace(" "+word[0].upper()+word[1:]," "+tr+" ")
        d = d.replace(" "+word," "+tr+" ")
    with open(name,"w",encoding='utf-8') as f:
        f.write(d)


def two():
    print("본 작업은 파일의 내용을 바꾸지 않습니다.")
    print("출력되는 내용을 프리앰블에 복붙해주세요")
    name = get_file_from_ch_name()
    with open(name,"r",encoding = 'utf-8') as f:
        d = f.read()
    criterion_two = re.compile(r'\\tr[A-Za-z]+')
    for i in [x for x in set(criterion_two.findall(d)) if (x not in jargon_list)]:
        print("\\newcommand{"+i+"}{} % ")

def db(match_obj):
    return match_obj.group(1)+'\\'+match_obj.group(2)

def three():
    print("!!주의!! 본 작업은 롤백이 안 됩니다.")
    name = get_file_from_ch_name()
    with open(name,"r",encoding='utf-8') as f:
        d = f.read()
    d = re.sub(r'(\\tr[A-Za-z]+)(이|가|을|를|와|과|로|으로|은|는|라|이라)',db,d)
    with open(name,"w",encoding='utf-8') as f:
        f.write(d)
    
def zero():
    print("preamble 스크레이핑 완료. ")
    print("!주의! 본 스크립트로 인한 변화는 롤백이 불가능합니다. 꼭 git commit 후 사용해주세요")
    print("1: 현재 preamble에 있는 용어를 특정 챕터에 적용")
    print("2: 특정 챕터에 있는 용어 중, preamble에 없는 것을 전부 프린트하기.")
    print("3: 특정 챕터의 텍스트에 자동 조사 붙이기")
    while True:
        a = input("어느 기능을 사용하시겠어요?\r\n")
        a = a.strip()
        if a == '1':
            one()
            break
        elif a == '2':
            two()
            break
        elif a == '3':
            three()
            break
        else:
            print("1, 2, 3 중 하나를 입력해주시기 바랍니다.")

if __name__=="__main__":
    zero()