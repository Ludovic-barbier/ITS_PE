# -*- coding: utf-8 -*-
"""preprocess_PE.ipynb

Automatically generated by Colaboratory.

Original file is located at
    https://colab.research.google.com/drive/1uY-ma83wFx0aRCF-e3wcK9x5oU4RCKNm
"""

import pandas as pd
import numpy as np

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

def extract_area(zone):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set 1\zone_area.csv', sep=";")
    return(data[data['ZONE']==zone]['AREA'].values)

def competences_from_zone(zone):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set 1\workload_by_competencies.csv', sep=";")
    areas = extract_area(zone)
    competences = []
    for i in areas:
        for j in range(data[data['AREA']==i]['COMPETENCY'].size):
            if data[data['AREA']==i]['COMPETENCY'].values[j] not in competences:
                competences.append(data[data['AREA']==i]['COMPETENCY'].values[j])
    return(competences)

def competences_from_area(area):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set 1\workload_by_competencies.csv', sep=";")
    competences = []
    for j in range(data[data['AREA']==area]['COMPETENCY'].size):
        if data[data['AREA']==area]['COMPETENCY'].values[j] not in competences:
            competences.append(data[data['AREA']==area]['COMPETENCY'].values[j])
    return(competences)

def creation_association_rule_area(tab_competence):
  file_to_read = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set 1\Association_Rule.csv', sep=';')
  tab_res_association_rule = np.zeros((len(tab_competence), len(tab_competence)), dtype=np.int8)
  for i in range(len(tab_competence)):
    #tab_res_association_rule[i+1][0] = extract_int(tab_competence[i])[0]
    for j in range(len(tab_competence)):
      #tab_res_association_rule[0][j+1] = extract_int(tab_competence[j])[0]
      if(extract_int(tab_competence[j])[0] <= extract_int(tab_competence[i])[0]):
        tab_res_association_rule[i][j] = extract_association_rule(tab_competence[i], tab_competence[j], file_to_read)
        tab_res_association_rule[j][i] = tab_res_association_rule[i][j]
  np.savetxt('res.csv', tab_res_association_rule, delimiter=';')

def workload_per_competences(tab_competence):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set 1\workload_by_competencies.csv', sep=";")
    workload = np.zeros(len(tab_competence))
    for i in range(len(tab_competence)):
        for j in range(data[data['COMPETENCY']==tab_competence[i]]['HOURLY WORKLOAD'].size):
            workload[i] = workload[i] + data[data['COMPETENCY']==tab_competence[i]]['HOURLY WORKLOAD'].values[0]
    np.savetxt('workload.csv', workload, delimiter=';', fmt='%.2f')

def min_op_max_op(tab_competence):
    data = pd.read_csv('Données Projet ST - EMSE Projet Etudiant\set 1\Interval_duplication_competency.csv', sep=';')
    list_min_op = np.zeros(len(tab_competence))
    list_max_op = np.zeros(len(tab_competence))
    for i in range(len(tab_competence)):
        list_min_op[i] = data[data['COMPETENCY']==tab_competence[i]]['MIN DUPLICATION'].values[0]
        list_max_op[i] = data[data['COMPETENCY']==tab_competence[i]]['MAX DUPLICATION'].values[0]
    np.savetxt('min_op.csv', list_min_op, delimiter=';')
    np.savetxt('max_op.csv', list_min_op, delimiter=';')

workload_per_competences(competences_from_area('AREA 8'))
creation_association_rule_area(competences_from_area('AREA 8'))
min_op_max_op(competences_from_area('AREA 8'))
