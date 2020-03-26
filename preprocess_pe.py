# -*- coding: utf-8 -*-
"""preprocess_PE.ipynb

Automatically generated by Colaboratory.

Original file is located at
    https://colab.research.google.com/drive/1uY-ma83wFx0aRCF-e3wcK9x5oU4RCKNm
"""

import pandas as pd
import numpy as np
from babel.numbers import format_decimal

def extract_int(competence):
    return([int(s) for s in competence.split() if s.isdigit()])

def extract_association_rule(competency1, competency2, data):
    data_cp1 = data[data['COMPETENCY 1']==competency1]
    data_cp2 = data_cp1[data_cp1['COMPETENCY 2']==competency2]
    if(data_cp2['ASSOCIATION RULE'].size > 0):
        if(data_cp2['ASSOCIATION RULE'].values[0] == "FORBIDDEN"):
            return 0
        else:
            return 1
    else:
        return False

def extract_area(set, zone):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set '+str(set)+'\zone_area.csv', sep=";")
    return(data[data['ZONE']==zone]['AREA'].values)

def competences_from_zone(set, zone):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set '+str(set)+'\workload_by_competencies.csv', sep=";")
    areas = extract_area(set, zone)
    competences = []
    for i in areas:
        for j in range(data[data['AREA']==i]['COMPETENCY'].size):
            if data[data['AREA']==i]['COMPETENCY'].values[j] not in competences:
                competences.append(data[data['AREA']==i]['COMPETENCY'].values[j])
    return(competences)

def competences_from_area(set, area):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set '+str(set)+'\workload_by_competencies.csv', sep=";")
    competences = []
    for j in range(data[data['AREA']==area]['COMPETENCY'].size):
        if data[data['AREA']==area]['COMPETENCY'].values[j] not in competences:
            competences.append(data[data['AREA']==area]['COMPETENCY'].values[j])
    return(competences)

def creation_association_rule(set, tab_competence):
  file_to_read = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set '+str(set)+'\Association_Rule.csv', sep=';')
  tab_res_association_rule = np.zeros((len(tab_competence), len(tab_competence)), dtype=np.int8)
  for i in range(len(tab_competence)):
    #tab_res_association_rule[i+1][0] = extract_int(tab_competence[i])[0]
    for j in range(len(tab_competence)):
      #tab_res_association_rule[0][j+1] = extract_int(tab_competence[j])[0]
      if(extract_int(tab_competence[j])[0] <= extract_int(tab_competence[i])[0]):
        tab_res_association_rule[i][j] = extract_association_rule(tab_competence[i], tab_competence[j], file_to_read)
        tab_res_association_rule[j][i] = tab_res_association_rule[i][j]
  return tab_res_association_rule

def workload_per_competences(set, tab_competence):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set '+str(set)+'\workload_by_competencies.csv', sep=";")
    workload = np.zeros(len(tab_competence))
    for i in range(len(tab_competence)):
        for j in range(data[data['COMPETENCY']==tab_competence[i]]['HOURLY WORKLOAD'].size):
            workload[i] = workload[i] + data[data['COMPETENCY']==tab_competence[i]]['HOURLY WORKLOAD'].values[0]
    return workload

def min_op_max_op(set, tab_competence):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set '+str(set)+'\Interval_duplication_competency.csv', sep=';')
    list_min_op = np.zeros(len(tab_competence))
    list_max_op = np.zeros(len(tab_competence))
    for i in range(len(tab_competence)):
        list_min_op[i] = data[data['COMPETENCY']==tab_competence[i]]['MIN DUPLICATION'].values[0]
        list_max_op[i] = data[data['COMPETENCY']==tab_competence[i]]['MAX DUPLICATION'].values[0]
    return list_min_op, list_max_op

def ratio_skills():
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\people_nb_competencies.csv', sep=';')
    ratio = []
    for i in range(data.filter(regex='OCR').size):
        ratio.append(data.values[0][i])
    return ratio

def create_file_from(set, type, name, nb, minVers, maxVers, time):
    if(type == 'zone'):
        file='ITS_PE.dat'
        with open(file, 'w') as filetowrite:

            workload = workload_per_competences(set, competences_from_zone(set, name))
            association_rule = creation_association_rule(set, competences_from_zone(set, name))
            liste_min_op, liste_max_op = min_op_max_op(set, competences_from_zone(set, name))
            ratio = ratio_skills()

            filetowrite.write('Operator = {')
            for i in range(0, nb-1):
                filetowrite.write(str(i)+',')
            filetowrite.write(str(nb-1)+'};\n')

            filetowrite.write('Competence = {')
            for i in range(0, len(workload)-1):
                filetowrite.write(str(i)+',')
            filetowrite.write(str(len(workload)-1)+'};\n')

            filetowrite.write('demand = [')
            for i in range(0, len(workload)-1):
                filetowrite.write(f'{int(workload[i])},')
            filetowrite.write(f'{int(workload[-1])}];\n')

            filetowrite.write('hourlyAvailability = [')
            for i in range(0, nb-1):
                filetowrite.write('1485.12,')
            filetowrite.write('1485.12];\n')

            filetowrite.write('minOperator = [')
            for i in range(0, len(liste_min_op)-1):
                filetowrite.write(f'{int(liste_min_op[i])},')
            filetowrite.write(f'{int(liste_min_op[-1])}];\n')

            filetowrite.write('maxOperator = [')
            for i in range(0, len(liste_max_op)-1):
                filetowrite.write(f'{int(liste_max_op[i])},')
            filetowrite.write(f'{int(liste_max_op[-1])}];\n')

            filetowrite.write(f'minVersatility = {int(minVers)};\n')
            filetowrite.write(f'maxVersatility = {int(maxVers)};\n')

            filetowrite.write('ratioSkills = [')
            for i in range(0, len(ratio)-1):
                filetowrite.write(str(ratio[i])+',')
            filetowrite.write(str(ratio[-1])+'];\n')

            filetowrite.write('timeRatio = '+str(time)+';\n')

            filetowrite.write('compatibility = [')
            for i in range(0, association_rule.shape[0]-1):
                filetowrite.write('[')
                for j in range(0, association_rule.shape[1]-1):
                    filetowrite.write(f'{int(association_rule[i][j])},')
                filetowrite.write(f'{int(association_rule[i][-1])}],')
            filetowrite.write('[')
            for j in range(0, association_rule.shape[1]-1):
                filetowrite.write(f'{int(association_rule[-1][j])},')
            filetowrite.write(f'{int(association_rule[-1][-1])}]];\n')

        filetowrite.close()
    elif(type == 'area'):
        file='ITS_PE.dat'
        with open(file, 'w') as filetowrite:

            workload = workload_per_competences(set, competences_from_area(set, name))
            association_rule = creation_association_rule(set, competences_from_area(set, name))
            liste_min_op, liste_max_op = min_op_max_op(set, competences_from_area(set, name))
            ratio = ratio_skills()

            filetowrite.write('Operator = {')
            for i in range(0, nb-1):
                filetowrite.write(str(i)+',')
            filetowrite.write(str(nb-1)+'};\n')

            filetowrite.write('Competence = {')
            for i in range(0, len(workload)-1):
                filetowrite.write(str(i)+',')
            filetowrite.write(str(len(workload)-1)+'};\n')

            filetowrite.write('demand = [')
            for i in range(0, len(workload)-1):
                filetowrite.write(f'{workload[i]},')
            filetowrite.write(f'{workload[-1]}];\n')

            filetowrite.write('hourlyAvailability = [')
            for i in range(0, nb-1):
                filetowrite.write('1485.12,')
            filetowrite.write('1485.12];\n')

            filetowrite.write('minOperator = [')
            for i in range(0, len(liste_min_op)-1):
                filetowrite.write(f'{int(liste_min_op[i])},')
            filetowrite.write(f'{int(liste_min_op[-1])}];\n')

            filetowrite.write('maxOperator = [')
            for i in range(0, len(liste_max_op)-1):
                filetowrite.write(f'{int(liste_max_op[-1])},')
            filetowrite.write(f'{int(liste_max_op[-1])}];\n')

            filetowrite.write(f'minVersatility = {int(minVers)};\n')
            filetowrite.write(f'maxVersatility = {int(maxVers)};\n')

            filetowrite.write('ratioSkills = [')
            for i in range(0, len(ratio)-1):
                filetowrite.write(str(ratio[i])+',')
            filetowrite.write(str(ratio[-1])+'];\n')

            filetowrite.write('timeRatio = '+str(time)+';\n')

            filetowrite.write('compatibility = [')
            for i in range(0, association_rule.shape[0]-1):
                filetowrite.write('[')
                for j in range(0, association_rule.shape[1]-1):
                    filetowrite.write(f'{int(association_rule[i][j])},')
                filetowrite.write(f'{int(association_rule[i][-1])}],')
            filetowrite.write('[')
            for j in range(0, association_rule.shape[1]-1):
                filetowrite.write(f'{int(association_rule[-1][j])},')
            filetowrite.write(f'{int(association_rule[-1][-1])}]];\n')

        filetowrite.close()
    else:
        print("WRONG TYPE")





#####################     CREATE FILES     ######################



create_file_from(2, 'zone', 'ZONE 3', 10, 1, 10, 0)
#create_file_from('zone', 'ZONE 7')


#####################     CREATE FILES     ######################














